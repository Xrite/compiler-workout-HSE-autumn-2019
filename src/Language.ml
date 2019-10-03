(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator
          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
     *)                                                       
    let int_to_bool i = match i with
      | 0 -> false
      | _ -> true

    let bool_to_int b = match b with
      | true -> 1
      | false -> 0

    let eval_one op l r =
      match op with
      | "+" -> l + r
      | "-" -> l - r
      | "*" -> l * r
      | "/" -> l / r
      | "%" -> l mod r
      | "<" -> bool_to_int (l < r)
      | ">" -> bool_to_int (l > r)
      | "<=" -> bool_to_int (l <= r)
      | ">=" -> bool_to_int (l >= r)
      | "==" -> bool_to_int (l = r)
      | "!=" -> bool_to_int (l <> r)
      | "&&" -> bool_to_int ((int_to_bool l) && (int_to_bool r))
      | "!!" -> bool_to_int ((int_to_bool l) || (int_to_bool r))

    let rec eval = fun s e -> match e with
      | Const c -> c
      | Var v -> s v
      | Binop (op, l, r) -> eval_one op (eval s l) (eval s r)

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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator
         val eval : config -> t -> config
       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (st, i, o) t = match t with
      | Read s -> let head :: tail = i in (Expr.update s head st, tail, o)
      | Write e -> (st, i, o @ [Expr.eval st e])
      | Assign (s, e) -> (Expr.update s (Expr.eval st e) st, i, o)
      | Seq (s1, s2) -> let c' = eval (st, i, o) s1 in eval c' s2

    (* Statement parser *)
    ostap (
      expr: !(Expr.parse);
      simple_stmt:
        "read" "(" x:IDENT ")" {Read x}
        | "write" "(" e:expr ")" {Write e}
        | x:IDENT ":=" e:expr {Assign (x, e)};

      parse: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun sl sr -> Seq (sl, sr)) s ss}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
