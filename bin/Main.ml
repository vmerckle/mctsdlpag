open Printf
module D = Dlpag
open Mctsdlpag
module S = Stdlib.Sys


(* arg parsing  *)
let verbose = ref false
let batch = ref false
let input_names = ref []
let filename = ref ""
let uctconstant = ref (sqrt 2.0)
let quicksolver = ref "neversmall" (*if --quicksolver is omitted*)
let quicksolverf = ref Deciders.neversmall
let solver = ref "simple"
let solverf = ref Simple.solve
let nplayout = ref 0

let speclist = [
("--quicksolver", Arg.Set_string quicksolver, "Quicksolver to use : propositional, allbutkleene, deterministic, smallsize, neversmall");
("--solver", Arg.Set_string solver, "Solver to use : MCTS, MCDS, simple, naive");
("-c", Arg.Set_float uctconstant, "UCT's constant");
("--nplayout", Arg.Set_int nplayout, "Number of playout per expansion");
("-v", Arg.Set verbose, "Output debug information");
("--batch", Arg.Set batch , "standardized output : value(-1:none, 0:false, 1:true), ...")
]
let usage_msg = "DL-PA Solver\nUsage : mctsdlpag <dlpa file>"
(* function to handle anonymous arguments *)
let add_name s = input_names := s :: !input_names

let arg_verify () =
  Arg.parse speclist add_name usage_msg;
  (match !input_names with
  | [n] -> filename := n 
  | _ -> failwith "Wrong number of arguments."
  );
  (quicksolverf := match !quicksolver with
    | "propositional" -> Deciders.propositional
    | "allbutkleene" -> Deciders.allbutkleene
    | "deterministic" -> Deciders.deterministic
    | "smallsize" -> Deciders.smallsize
    | "neversmall" -> Deciders.neversmall
    | _ -> failwith "Wrong quicksolver");
  let foreverN = max_int in
  (solverf := match !solver with
    | "MCTS" -> MCTS.solve ~n:foreverN ~constant:!uctconstant ~quicksolver:(!quicksolver)
    | "MCDS" -> MCDSv2.solve ~n:foreverN ~quicksolver:(!quicksolverf) ~constant:!uctconstant
    | "MCDSn" -> MCDSv2_exp.solve ~n:foreverN ~quicksolver:(!quicksolverf) ~constant:!uctconstant ~playout:!nplayout
    | "simple" -> Simple.solve
    | "naive" -> MCTSutils.solve
    | s -> failwith (sprintf "Wrong solver:%s" s))

let get_formula () = 
  let p = D.Parse.from_file () !filename in
  (*printf "%s\n\n" (D.Ast.Print.file p);*)
  let g = D.Circuit.file p in
  let old_f = D.Formula.file g in
  old_f
  (*Formula.formula_retread old_f*)


let print_bool_option = function
  | None -> sprintf "NONE"
  | Some b -> sprintf "%B" b
let batch_bool_option = function
  | None -> "none"
  | Some true -> "true"
  | Some false -> "false"

let start () = 
  let _ = Random.self_init() in
  arg_verify ();
  let old_f = get_formula () in
  let _ = if not !batch then
    printf "solver :%s, quicksolver : %s, constant :%f\n" !solver !quicksolver !uctconstant else () in
  let bo, others = !solverf old_f in
  let otherS = String.concat "," others in
  if not !batch then
    printf "Result on %s : %s\nOther : %s\n" !filename (print_bool_option bo) otherS
  else printf "%s" (String.concat "," ((batch_bool_option bo)::others))


  (*
let start () =
  let _ = Random.self_init() in
  let dcircuit, _ = get_formula () in (*Dlpag.Formula.formula*)
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let _ = printf "Abdallah' solver : %B in %fs\n" babdallah tabdallah in ()



let start_debug () =
  let _ = Random.self_init() in
  let dcircuit, (old_f:Dlpag.Formula.formula) = get_formula () in
  let new_f = Formula.formula_retread old_f in
  (*let _= printf "New print :\n%s\n\n" (Formula.Print.formula new_f) in*)
  let fsize = Helper.size new_f in
  let _ = printf "Formula' size: %d\n" fsize in
  (* let _ = printf "Variable used : %s\n" (Formula.Print.ss (Helper.variables_in_f new_f)) in *)
  let res_simple, time_simple = Bench.time Simple.solve new_f in 
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let treeN =  100000 in
  let (res_mcdsv2, _), time_mcdsv2 = Bench.time (MCDSv2.solve new_f) treeN in 
  let _= printf "Simple : %s in %fs\n" (print_bool_option res_simple) time_simple in
  let _= printf "MCDSv2 : %s in %fs\n" (print_bool_option res_mcdsv2) time_mcdsv2 in
  let _ = printf "Abdallah' solver : %B in %fs\n" babdallah tabdallah in
  ()
(*
let start_simple () =
  let _ = Random.self_init() in
  let _, (old_f:Dlpag.Formula.formula) = get_formula () in
  let new_f = Formula.formula_retread old_f in
  (*let _= printf "New print :\n%s\n\n" (Formula.Print.formula new_f) in*)
  let fsize = Helper.size new_f in
  let _ = printf "Formula' size: %d\n" fsize in
  (* let _ = printf "Variable used : %s\n" (Formula.Print.ss (Helper.variables_in_f new_f)) in *)
  let treeN =  10000000 in
  let n = 1 in
  let _ = printf "Simple : %fs\n" (bench n Simple.solve_std new_f) in
  (*let _ = printf "MCTS(no transposition) : %fs\n" (bench n (MCTS.solve old_f) treeN) in*)
  let _ = printf "MCDS(no oracle) : %fs\n" (bench n (MCDSv2.solve new_f) treeN) in
  let _ = printf "notmodal : %fs\n" (bench n (MCDS_notmodal.solve new_f) treeN) in
  let _ = printf "allbutkleene : %fs\n" (bench n (MCDS_allbutkleene.solve new_f) treeN) in
  let _ = printf "deteronly : %fs\n" (bench n (MCDS_deteronly.solve new_f) treeN) in
  let _ = printf "size : %fs\n" (bench n (MCDS_size.solve new_f) treeN) in
  ()
*)
*)

let () = start ()
