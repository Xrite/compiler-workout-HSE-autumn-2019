open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (stack, conf) = function
  | [] -> stack, conf
  | (BINOP op)::ps ->
    let y::x::xs = stack in
    let res      = Expr.eval_one op x y in
    eval env (res::xs, conf) ps
  | (CONST c)::ps ->
    eval env (c::stack, conf) ps
  | READ::ps ->
    let s, i, o = conf in
    let z::zs   = i in
    eval env (z::stack, (s, zs, o)) ps
  | WRITE::ps ->
    let s, i, o = conf in
    let z::zs   = stack in
    eval env (zs, (s, i, o @ [z])) ps
  | (LD x)::ps ->
    let s, _, _ = conf in
    eval env ((s x)::stack, conf) ps
  | (ST x)::ps ->
    let s, i, o = conf in
    let z::zs   = stack in
    eval env (zs, (Expr.update x z s, i, o)) ps
  | (LABEL l)::ps ->
    eval env (stack, conf) ps 
  | (JMP l)::ps ->
    eval env (stack, conf) (env#labeled l)
  | (CJMP ("z", l))::ps -> 
    let z::zs = stack in
    eval env (stack, conf) (if z == 0 then env#labeled l else ps)
  | (CJMP ("nz", l))::ps -> 
    let z::zs = stack in
    eval env (stack, conf) (if z != 0 then env#labeled l else ps)
  | (CJMP (cc, l))::ps -> failwith ("Unknown CJMP argument: " ^ cc)


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)


class ast_env =
  object (self)
    val labels_cnt = 0

    method new_else_label = "else_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_fi_label = "fi_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_do_label = "do_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}
        
    method new_od_label = "od_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_rep_label = "rep_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}
  end

let rec compile_with_env (env : ast_env) =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)   -> let env', sm_s1  = compile_with_env env s1 in
                           let env'', sm_s2 = compile_with_env env' s2 in
                           env'', sm_s1 @ sm_s2
  | Stmt.Read x         -> env, [READ; ST x]
  | Stmt.Write e        -> env, expr e @ [WRITE]
  | Stmt.Assign (x, e)  -> env, expr e @ [ST x]
  | Stmt.Skip           -> env, []
  | Stmt.If (e, s1, s2) -> let label_else, env1 = env#new_else_label in
                           let label_fi, env2   = env1#new_fi_label in
                           let env3, sm_s1      = compile_with_env env2 s1 in
                           let env4, sm_s2      = compile_with_env env3 s2 in
                           env4, expr e @ [CJMP ("z", label_else)] @ sm_s1 @ [JMP label_fi; LABEL label_else] @ sm_s2 @ [LABEL label_fi]
  | Stmt.While (e, s)   -> let label_do, env1 = env#new_do_label in
                           let label_od, env2 = env1#new_od_label in
                           let env3, sm_s     = compile_with_env env2 s in
                           env3, [LABEL label_do] @ expr e @ [CJMP ("z", label_od)] @ sm_s @ [JMP label_do; LABEL label_od]
  | Stmt.Repeat (s, e)  -> let label_rep, env' = env#new_rep_label in
                           let env'', sm_s     = compile_with_env env' s in
                           env'', [LABEL label_rep] @ sm_s @ expr e @ [CJMP ("z", label_rep)]

let compile ast = let _, prog = compile_with_env (new ast_env) ast in prog
