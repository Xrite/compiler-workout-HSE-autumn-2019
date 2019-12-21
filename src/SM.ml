open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
  let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg =
         match prg with
         | [] -> 
                         conf
         | (BINOP op)::rest ->
                         let y::x::xs = stack in
                         let res      = Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) in
                         (eval env (cstack, res::xs, c) rest)
         | (CONST n)::rest ->
                         eval env (cstack, (Value.of_int n)::stack, c) rest
         | (STRING s)::rest ->
                         eval env (cstack, (Value.of_string @@ Bytes.of_string s)::stack, c) rest
         | (SEXP (t, n))::rest ->
                         let is, stack = split n stack in
                         eval env (cstack, (Value.sexp t (List.rev is))::stack, c) rest
         | (LD x)::rest ->
                         (eval env (cstack, (State.eval st x)::stack, c) rest)
         | (ST x)::rest ->
                         let z::zs   = stack in
                         (eval env (cstack, zs, (State.update x z st, i, o)) rest)
         | (STA (a, n))::rest ->
                         let z::stack = stack in 
			 let is, stack = split n stack in
                         eval env (cstack, stack, (Stmt.update st a z (List.rev is), i, o)) rest
         | (LABEL l)::rest ->
                         eval env conf rest 
         | (JMP l)::rest ->
                         (eval env conf (env#labeled l))
         | (CJMP ("z", l))::rest -> 
                         let z::zs = stack in
                         (eval env (cstack, zs, c) (if (Value.to_int z) == 0 then env#labeled l else rest))
         | (CJMP ("nz", l))::rest -> 
                         let z::zs = stack in
                         (eval env (cstack, zs, c) (if (Value.to_int z) != 0 then env#labeled l else rest))
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
			 if env#is_label f then
                                (Printf.printf "Func: %s\n";
                         	(eval env ((rest, st)::cstack, stack, c) (env#labeled f)))
			 else 
                         	eval env (env#builtin conf f n p) rest
         | (END)::_ -> 
                         (match cstack with 
                         | [] -> conf
                         | (rest', st')::cs_rest ->
                                 let new_st = State.leave st st' in
                                 eval env (cs_rest, stack, (new_st, i, o)) rest')
         | (RET p)::_ ->
                         (eval env conf [END])
         | (DROP)::rest ->
                         let _::zs = stack in
                         eval env (cstack, zs, c) rest
         | (DUP)::rest -> 
                         let z::zs = stack in
                         eval env (cstack, z::stack, c) rest
         | (SWAP)::rest ->
                         let a::b::zs = stack in
                         eval env (cstack, b::a::zs, c) rest
         | (TAG t)::rest -> 
                         let z::zs = stack in
                         let res = 
                                 (match z with
                                 | Value.Sexp (t', _) when t' = t -> 1
                                 | _ -> 0)
                         in
                         eval env (cstack, (Value.of_int res)::zs, c) rest
         | (ENTER xs)::rest ->
                         eval env (cstack, stack, (State.push st State.undefined xs, i, o)) rest
         | (LEAVE)::rest ->
                         eval env (cstack, stack, (State.drop st, i, o)) rest
         | other::_ -> failwith @@ show_insn other

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

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

     method new_case_label = "case_" ^ (string_of_int labels_cnt), {< labels_cnt = labels_cnt + 1 >}

     method proc_label f = "L" ^ f

     method func_label f = "L" ^ f

     method case_i label i = label ^ "_" ^ (string_of_int i)
   end


let rec match_pattern fail_label ids = function
        | Stmt.Pattern.Wildcard -> 
                        []
        | Stmt.Pattern.Ident _ ->
                        []
        | Stmt.Pattern.Sexp (t, ps) ->
                        let get_elem ids = List.flatten @@ List.map (fun i -> [CONST i; CALL (".elem", 2, false)]) ids in
                        let args = List.flatten @@ List.mapi (fun i p -> match_pattern fail_label (ids @ [i]) p) ps in 
                        [DUP] @ get_elem ids @
                        [DUP; TAG t; CJMP ("z", fail_label)] @
                        [DUP; CALL (".length", 1, false); CONST (List.length ps); BINOP "-"; CJMP ("nz", fail_label)] @ 
                        [DROP] @ args

let rec mk_scope = function
        | Stmt.Pattern.Wildcard ->
                        [DROP]
        | Stmt.Pattern.Ident x ->
                        [ST x]
        | Stmt.Pattern.Sexp (t, ps) ->
                        let args = List.flatten @@ List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ mk_scope p) ps in 
                        args @ [DROP]



 let rec compile_stmt (env : ast_env) =
   let rec compile_expr = function
   | Expr.Var   x          -> 
                   [LD x]
   | Expr.Const n          -> 
                   [CONST n]
   | Expr.Array es ->
                   let args = List.flatten (List.map compile_expr es) in
		   args @ [CALL (".array", List.length es, false)]
   | Expr.String s ->
		   [STRING s]
   | Expr.Sexp (t, es) ->
                   let args = List.flatten (List.map compile_expr es) in
		   args @ [SEXP (t, List.length es)]
   | Expr.Binop (op, x, y) -> 
                   compile_expr x @ compile_expr y @ [BINOP op]
   | Expr.Call (f, es)     -> 
                   let args = List.flatten (List.map compile_expr es) in
                   args @ [CALL (env#func_label f, List.length es, false)]
   | Expr.Elem (arr, e)     -> 
                   compile_expr arr @ compile_expr e @ [CALL (".elem", 2, false)]
   | Expr.Length e -> 
                   compile_expr e @ [CALL (".length", 1, false)]

   in
   function
   | Stmt.Seq (s1, s2)   -> 
                   let env', sm_s1  = compile_stmt env s1 in
                   let env'', sm_s2 = compile_stmt env' s2 in
                   env'', sm_s1 @ sm_s2
   | Stmt.Assign (x, is, e) -> 
		   (match is with
                    | [] -> 
		    		env, compile_expr e @ [ST x]
                    | is -> 
				let n = List.length is in
				let is = List.flatten (List.map compile_expr is) in
				env, (is @ compile_expr e @ [STA (x, n)]))
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
                   env, args @ [CALL (env#func_label f, List.length es, true)]
   | Stmt.Return None ->
                   env, [RET false]
   | Stmt.Return (Some e) ->
                   env, compile_expr e @ [RET true]
   | Stmt.Case (e, ps) ->
                   let case_label, env = env#new_case_label in
                   let rec compile_cases env case_num = function
                           | [] -> 
                                           env, []
                           | (p, s)::rest -> 
                                           let env, compiled_s = compile_stmt env s in
                                           let env, compiled_rest = compile_cases env (case_num + 1) rest in
                                           let next_label = env#case_i case_label case_num in
                                           let compiled_branch = 
                                                   match_pattern next_label [] p @ [ENTER (Stmt.Pattern.vars p)] @ mk_scope p @
                                                   compiled_s @ [LEAVE; JMP case_label; LABEL next_label; DROP]
                                           in
                                           env, compiled_branch @ compiled_rest
                   in
                   let env, compiled = compile_cases env 0 ps in
                   env, compile_expr e @ compiled @ [LABEL case_label]
   | Stmt.Leave -> 
                   env, [LEAVE]


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
