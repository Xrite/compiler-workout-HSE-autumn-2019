open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let eval_step (st, conf) step =
  match step with
  | BINOP op ->
    let x :: y :: tail = st in
    let res = Language.Expr.eval_one op x y in
    (res :: tail, conf)
  | CONST c ->
    (c :: st, conf)
  | READ ->
    let (s, i, o) = conf in
    let z :: rest = i in
    (z :: st, (s, rest, o))
  | WRITE ->
    let (s, i, o) = conf in
    let z :: rest = st in
    (rest, (s, i, o @ [z]))
  | LD x ->
    let (s, _, _) = conf in
    (s x :: st, conf)
  | ST x ->
    let (s, i, o) = conf in
    let z :: rest = st in
    (rest, (Language.Expr.update x z s, i, o))

let rec eval c p =
  match p with
  | [] -> c
  | step :: rest -> eval (eval_step c step) rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec compile_expr expr =
    match expr with
    | Language.Expr.Const c -> [CONST c]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_expr e2 @ compile_expr e1 @ [BINOP op]
  in
  match stmt with
  | Language.Stmt.Read x -> [READ; ST x]
  | Language.Stmt.Write e -> compile_expr e @ [WRITE]
  | Language.Stmt.Assign (x, e) -> compile_expr e @ [ST x]
  | Language.Stmt.Seq (s1, s2) -> compile s1 @ compile s2
