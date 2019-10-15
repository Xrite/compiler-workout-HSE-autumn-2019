(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
    primary: x:IDENT {Var x} | c:DECIMAL {Const c} | -"(" parse -")"
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let rec eval env ((st, i, o) as conf) t = match t with
      | Read s -> let head :: tail = i in (State.update s head st, tail, o)
      | Write e -> (st, i, o @ [Expr.eval st e])
      | Assign (s, e) -> (State.update s (Expr.eval st e) st, i, o)
      | Seq (s1, s2) -> let c' = eval env (st, i, o) s1 in eval env c' s2
      | Skip -> conf
      | If (cond, s1, s2) -> eval env (st, i, o) (if Expr.eval st cond == 1 then s1 else s2)
      | While (cond, s) -> if Expr.eval st cond == 0 then conf else eval env conf (Seq (s, While (cond, s)))
      | Repeat (s, cond) -> let (st', _, _) as conf' = eval env conf s in
                            if Expr.eval st' cond != 0 then conf' else eval env conf' (Repeat (s, cond))
      | Call (f, args_e) -> let (args, locals, body) = env#definition f in
                            let update_st = fun s a e -> State.update a (Expr.eval st e) s in
                            let st_enter = State.push_scope st (args @ locals) in
                            let st_sub = List.fold_left2 update_st st_enter args args_e in
                            let st', i', o' = eval env (st_sub, i, o) body in
                            State.drop_scope st' st, i', o'



    let rec build_if elifs els = 
            match elifs with
            | (cond, s)::es -> If (cond, s, build_if es els)
            | [] -> match els with
                    | None -> Skip
                    | Some s' -> s'

    let build_for s1 e s2 s3 = Seq (s1, While (e, Seq (s3, s2)))
                                
    (* Statement parser *)
    ostap (
      expr: !(Expr.parse);
      simple_stmt: read | write | assign | skip | if_stmt | while_stmt | repeat_stmt | for_stmt | call;

      read: "read" "(" x:IDENT ")" {Read x};
      write: "write" "(" e:expr ")" {Write e};
      assign: x:IDENT ":=" e:expr {Assign (x, e)};
      skip: "skip" {Skip};
      if_stmt: "if" e:expr "then" s:parse elifs:elif_block* els:else_block? "fi" {If (e, s, build_if elifs els)};
      else_block: -"else" parse;
      elif_block: -"elif" expr -"then" parse;
      while_stmt: "while" e:expr "do" s:parse "od" {While (e, s)};
      repeat_stmt: "repeat" s:parse "until" e:expr {Repeat (s, e)};
      for_stmt: "for" s1:parse "," e:expr "," s2:parse "do" s3:parse "od" {build_for s1 e s2 s3};

      parse_args: !(Util.list0By)[ostap (",")][expr];
      call: name:IDENT "(" args:parse_args ")" {Call (name, args)};

      parse: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun sl sr -> Seq (sl, sr)) s ss}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      ident: IDENT;
      parse_args: !(Util.list0By)[ostap (",")][ident];
      parse_some_locals: -"local" !(Util.listBy)[ostap (",")][ident];
      parse_locals: l:parse_some_locals? {match l with | None -> [] | Some ls -> ls};
      parse: "fun" name:IDENT "(" args:parse_args ")" locals:parse_locals "{" body:!(Stmt.parse) "}"
        {name, (args, locals, body)}
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
