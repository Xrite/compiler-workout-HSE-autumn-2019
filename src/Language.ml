(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = List.init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
    | s -> failwith (Printf.sprintf "No such builtin: %s" s)
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval env ((st, i, o, r) as conf) expr =
            match expr with
            | Const n -> 
                            (st, i, o, Some (Value.of_int n))
            | Array es ->
                            let (st, i, o, vs) as conf = eval_list env conf es in
                            Builtin.eval conf vs "$array"
            | String s -> 
                            (st, i, o, Some (Value.of_string s))
            | Sexp (_, _) -> failwith "NOOOOOO! YOU CANT USE THIS!"
            | Var   x -> 
                            (st, i, o, Some (State.eval st x))
            | Binop (op, x, y) -> 
                            let (_, _, _, Some a) as c' = eval env conf x in
                            let (s'', i'', o'', Some b) = eval env c' y in
                            s'', i'', o'', Some (Value.of_int (to_func op (Value.to_int a) (Value.to_int b)))
            | Elem (arr, e) -> 
                            let (st, i, o, Some a) as conf = eval env conf arr in
                            let (st, i, o, Some v) as conf = eval env conf e in
                            Builtin.eval conf [a; v] "$elem"
            | Length e -> 
                            let (st, i, o, Some a) as conf = eval env conf e in
                            Builtin.eval conf [a] "$length"
            | Call (f, es) -> 
                            let eval_step = fun (cfg, vs) e -> let (_, _, _, Some v) as cfg' = eval env cfg e in cfg', v::vs in
                            let conf', vs_r = List.fold_left eval_step (conf, []) es in
                            env#definition env f (List.rev vs_r) conf'

    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
             in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
         !(Util.expr
       	    (fun x -> x)
 	    [|
 	      `Lefta, [
 	        ostap("!!"), fun x y -> Binop ("!!", x, y)
 	      ];
 	      `Lefta, [
 	        ostap("&&"), fun x y -> Binop ("&&", x, y)
 	      ];
 	      `Nona, [
 	        ostap("=="), (fun x y -> Binop ("==", x, y));
 	        ostap("!="), (fun x y -> Binop ("!=", x, y));
 	        ostap("<="), (fun x y -> Binop ("<=", x, y));
 	        ostap("<"),  (fun x y -> Binop ("<", x, y));
 	        ostap(">="), (fun x y -> Binop (">=", x, y));
 	        ostap(">"),  (fun x y -> Binop (">", x, y));
 	      ];
 	      `Lefta, [
 	        ostap("+"), (fun x y -> Binop ("+", x, y));
 	        ostap("-"), (fun x y -> Binop ("-", x, y));
 	      ];
 	      `Lefta, [
 	        ostap("*"), (fun x y -> Binop ("*", x, y));
 	        ostap("/"), (fun x y -> Binop ("/", x, y));
 	        ostap("%"), (fun x y -> Binop ("%", x, y));
 	      ];
 	    |]
 	    primary
          );
       primary: parse_var | parse_const | parse_call | parse_parens | parse_elem | parse_array | parse_length | parse_string | parse_char;

       parse_var: x:IDENT {Var x};
       parse_const: c:DECIMAL {Const c};
       parse_parens: -"(" parse -")";

       parse_call: name:IDENT "(" args:parse_args ")" {Call (name, args)};
       parse_args: !(Util.list0By)[ostap (",")][parse];

       parse_elem: arr:parse "[" e:parse "]" {Elem (arr, e)};
       parse_array: "[" args:parse_args "]" {Array args};
       parse_length: e:parse ".length" {Length e};

       parse_string: s:STRING {String (String.sub s 1 (String.length s - 2))};
       parse_char: c:CHAR {Const (Char.code c)}
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
          
    let rec eval env ((st, i, o, r) as conf) k stmt = 
	    let (<|>) s1 s2 = 
		    match s2 with
		    | Skip -> s1
		    | _ -> Seq (s1, s2) 
	    in
	    match stmt with
	    | Assign (x, is, e) -> 
                            let (st, i, o, is) as conf = Expr.eval_list env conf is in
                            let (st, i, o, Some v) as conf = Expr.eval env (st, i, o, None) e in
			    eval env (update st x v is, i, o, None) Skip k
	    | Seq (s1, s2) -> 
			    eval env conf (s2 <|> k) s1
	    | Skip -> 
			    (match k with
			    | Skip -> conf
			    | _    -> eval env conf Skip k)
	    | If (e, s1, s2) -> 
			    let st, i, o, Some n = Expr.eval env conf e in
			    if (Value.to_int n) != 0 then
				    eval env (st, i, o, None) k s1
    			    else
	    			    eval env (st, i, o, None) k s2
	    | While (e, s) -> 
			    let st, i, o, Some n = Expr.eval env conf e in
			    if (Value.to_int n) != 0 then
				    eval env (st, i, o, None) (While (e, s) <|> k) s
			    else
				    eval env (st, i, o, None) Skip k
	    | Repeat (s, e) -> 
			    let negate e = Expr.Binop ("==", e, Expr.Const 0) in
			    eval env conf (While (negate e, s) <|> k) s
	    | Call (f, es) -> 
			    let eval_step = fun (cfg, vs) e -> let (_, _, _, Some v) as cfg' = Expr.eval env cfg e in cfg', v::vs in
			    let conf', vs_r = List.fold_left eval_step (conf, []) es in
			    eval env (env#definition env f (List.rev vs_r) conf') Skip k
	    | Return None ->
			    conf
	    | Return (Some e) ->
			    Expr.eval env conf e
	    | _ -> failwith "Unknown command"  

    let rec build_if elifs els = 
            match elifs with
             | (cond, s)::es -> 
                             If (cond, s, build_if es els)
             | [] -> 
                             match els with
                             | None -> Skip
                             | Some s' -> s'

     let build_for s1 e s2 s3 = Seq (s1, While (e, Seq (s3, s2)))

         
    (* Statement parser *)
    ostap (
      expr: !(Expr.parse);
      simple_stmt: assign | skip | if_stmt | while_stmt | repeat_stmt | for_stmt | call | return;

      assign: x:IDENT is:(-"[" expr -"]")* ":=" e:expr {Assign (x, is, e)};
      skip: "skip" {Skip};
      if_stmt: "if" e:expr "then" s:parse elifs:elif_block* els:else_block? "fi" {If (e, s, build_if elifs els)};
      else_block: -"else" parse;
      elif_block: -"elif" expr -"then" parse;
      while_stmt: "while" e:expr "do" s:parse "od" {While (e, s)};
      repeat_stmt: "repeat" s:parse "until" e:expr {Repeat (s, e)};
      for_stmt: "for" s1:parse "," e:expr "," s2:parse "do" s3:parse "od" {build_for s1 e s2 s3};

      parse_args: !(Util.list0By)[ostap (",")][expr];
      call: name:IDENT "(" args:parse_args ")" {Call (name, args)};

      return: "return" e:expr? {Return e};

      parse: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun sl sr -> Seq (sl, sr)) s ss}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
