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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg =
        match prg with
        | [] -> 
                        conf
        | (BINOP op)::rest ->
                        let y::x::xs = stack in
                        let res      = Expr.to_func op x y in
                        (eval env (cstack, res::xs, c) rest)
        | (CONST n)::rest ->
                        eval env (cstack, n::stack, c) rest
        | READ::rest ->
                        let z::zs = i in
                        (eval env (cstack, z::stack, (st, zs, o)) rest)
        | WRITE::rest ->
                        let z::zs   = stack in
                        (eval env (cstack, zs, (st, i, o @ [z])) rest)
        | (LD x)::rest ->
                        (eval env (cstack, (State.eval st x)::stack, c) rest)
        | (ST x)::rest ->
                        let z::zs   = stack in
                        (eval env (cstack, zs, (State.update x z st, i, o)) rest)
        | (LABEL l)::rest ->
                        eval env conf rest 
        | (JMP l)::rest ->
                        (eval env conf (env#labeled l))
        | (CJMP ("z", l))::rest -> 
                        let z::zs = stack in
                        (eval env (cstack, zs, c) (if z == 0 then env#labeled l else rest))
        | (CJMP ("nz", l))::rest -> 
                        let z::zs = stack in
                        (eval env (cstack, zs, c) (if z != 0 then env#labeled l else rest))
        | (CJMP (cc, l))::rest -> 
                        failwith ("Unknown CJMP argument: " ^ cc)
        | (BEGIN (f, args, locals))::rest -> 
                        let n = List.length args in
                        let rec split n = function
                                | xs when n == 0 -> ([], xs)
                                | x::xs -> let fs, ss = split (n - 1) xs in x::fs, ss
                        in 
                        let zs_r, rest_stack = split n stack in
                        let zs =  List.rev zs_r in
                        let update_st = fun s a e -> State.update a e s in
                        let st_enter = State.enter st (args @ locals) in
                        let st_sub = List.fold_left2 update_st st_enter args zs in
                        (eval env (cstack, rest_stack, (st_sub, i, o)) rest)
        | (CALL (f, n, p))::rest -> 
                        (eval env ((rest, st)::cstack, stack, c) (env#labeled f))
        | (END)::_ -> 
                        (match cstack with 
                        | [] -> conf
                        | (rest', st')::cs_rest ->
                                let new_st = State.leave st st' in
                                eval env (cs_rest, stack, (new_st, i, o)) rest')
        | (RET p)::_ ->
                        (eval env conf [END])


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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = failwith "Not implemented"
class ast_env =
  object (self)
    val labels_cnt = 0

    method new_else_label = "else_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_fi_label = "fi_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_do_label = "do_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_od_label = "od_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method new_rep_label = "rep_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

    method proc_label f = "proc_" ^ f

    method func_label f = "func_" ^ f
  end

let rec compile_stmt (env : ast_env) =
  let rec compile_expr = function
  | Expr.Var   x          -> 
                  [LD x]
  | Expr.Const n          -> 
                  [CONST n]
  | Expr.Binop (op, x, y) -> 
                  compile_expr x @ compile_expr y @ [BINOP op]
  | Expr.Call (f, es)     -> 
                  let args = List.flatten (List.map compile_expr es) in
                  args @ [CALL (env#func_label f, List.length es, true)]

  in
  function
  | Stmt.Seq (s1, s2)   -> 
                  let env', sm_s1  = compile_stmt env s1 in
                  let env'', sm_s2 = compile_stmt env' s2 in
                  env'', sm_s1 @ sm_s2
  | Stmt.Read x         -> 
                  env, [READ; ST x]
  | Stmt.Write e        -> 
                  env, compile_expr e @ [WRITE]
  | Stmt.Assign (x, e)  -> 
                  env, compile_expr e @ [ST x]
  | Stmt.Skip           -> 
                  env, []
  | Stmt.If (e, s1, s2) -> 
                  let label_else, env1 = env#new_else_label in
                  let label_fi, env2   = env1#new_fi_label in
                  let env3, sm_s1      = compile_stmt env2 s1 in
                  let env4, sm_s2      = compile_stmt env3 s2 in
                  env4, compile_expr e @ [CJMP ("z", label_else)] @ sm_s1 @ [JMP label_fi; LABEL label_else] @ sm_s2 @ [LABEL label_fi]
  | Stmt.While (e, s)   -> 
                  let label_do, env1 = env#new_do_label in
                  let label_od, env2 = env1#new_od_label in
                  let env3, sm_s     = compile_stmt env2 s in
                  env3, [LABEL label_do] @ compile_expr e @ [CJMP ("z", label_od)] @ sm_s @ [JMP label_do; LABEL label_od]
  | Stmt.Repeat (s, e)  -> 
                  let label_rep, env' = env#new_rep_label in
                  let env'', sm_s     = compile_stmt env' s in
                  env'', [LABEL label_rep] @ sm_s @ compile_expr e @ [CJMP ("z", label_rep)]
  | Stmt.Call (f, es)   -> 
                  let args = List.flatten (List.map compile_expr es) in
                  env, args @ [CALL (env#func_label f, List.length es, false)]
  | Stmt.Return None ->
                  env, [RET false]
  | Stmt.Return (Some e) ->
                  env, compile_expr e @ [RET true]


let rec compile_definitions (env : ast_env) = function
  | [] -> env, []
  | (f, (args, locals, body))::rest ->
        let env', compiled_body  = compile_stmt env body in
        let env'', compiled_rest = compile_definitions env' rest in
        env'', [LABEL (env#func_label f); BEGIN (env#func_label f, args, locals)] @ compiled_body @ [END] @ compiled_rest

let compile ast = 
        let definitions, stmts = ast in
        let env, compiled_definitions = compile_definitions (new ast_env) definitions in
        let _, compiled_stmts = compile_stmt env stmts in
        compiled_stmts @ [END] @ compiled_definitions 
