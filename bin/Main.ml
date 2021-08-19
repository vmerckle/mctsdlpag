open Printf
module D = Dlpag
open Mctsdlpag

let verbose = ref false

let get_filename () =
  let speclist = [("-v", Arg.Set verbose, "Output debug information")] in
  let usage_msg = "DL-PA Solver\nUsage : mctsdlpag <dlpa file>" in
  let input_names = ref [] in
  let add_name s = input_names := s :: !input_names in
  Arg.parse speclist add_name usage_msg;
  match !input_names with
  | [n] -> n 
  | _ -> failwith "Wrong number of arguments."

let time f x =
  let t = Sys.time() in
  let fx = f x  in fx, Sys.time() -. t

let get_formula () = 
  let f = get_filename () in
  let p = D.Parse.from_file () f in
  (*printf "%s\n\n" (D.Ast.Print.file p);*)
  let g = D.Circuit.file p in
  g, D.Formula.file g

(* let start () =
  let _ = Random.self_init() in
  let dcircuit, df = get_formula () in (*Dlpag.Formula.formula*)
  let f = MCTSutils.formToIForm df in
  let tree = MCTSutils.splitIF (MCTSutils.SS.empty) f in
  let _= printf "\nInput formula : %s \n" (D.Formula.Print.formula df) in
  let _= printf "it has %d variables.\n\n" (MCTSutils.acountF df) in
  let _= printf "Internal formula : %s \n" (MCTSutils.Print.iformula f) in
  let _= printf "After one split : \n%s\nPlaythrough now\n\n" (MCTSutils.Print.arbre tree) in
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let bbrute, tbrute = time (MCTSutils.solve df false) 0 in
  let  nn = 2000000 in
  let (bdag, dcount), tdag = time (MCDS.solve df) nn in let _= match bdag with
    MCTSutils.Proven b -> printf "\n%B : DAG. in %d steps\n" b dcount
  | MCTSutils.Ni -> printf " \nNo answer : DAG. in %d steps\n" dcount
  in 
  let (bmcts,count), tmcts = time (MCTS.solve df) nn in let _= match bmcts with
    MCTSutils.Proven b -> printf "%B : MCTS. in %d steps\n" b count
  | MCTSutils.Ni -> printf " No answer : MCTS. in %d steps\n" count
  in
(*  let bnew, tnew = time (Treev2.solve df true) nn in let _ = match bnew with
    | None -> printf "New solver has no answer after %fs\n" tnew
    | Some b -> printf "New solver found %B after %fs\n" b tnew
  in  *)
  let _= printf "%B : Abdallah's naive solver found\n" babdallah in
  let _ = printf "%B : Brute playthrough" bbrute in 
  ignore (printf "Abdallah : %fs, Brute : %fs, Mcts : %fs, Dag : %fs\n" tabdallah tbrute tmcts tdag)
*)

let print_bool_option = function
  | None -> sprintf "None"
  | Some b -> sprintf "%B" b

let start () =
  let _ = Random.self_init() in
  let dcircuit, _ = get_formula () in (*Dlpag.Formula.formula*)
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let _ = printf "Abdallah' solver : %B in %fs\n" babdallah tabdallah in ()


let start_simple () =
  let _ = Random.self_init() in
  let dcircuit, (old_f:Dlpag.Formula.formula) = get_formula () in
  let new_f = Formula.formula_retread old_f in

  (*let _= printf "New print :\n%s\n\n" (Formula.Print.formula new_f) in*)
  let res_simple, time_simple = time Simple.solve new_f in 
  let _= printf "Simple : %s in %fs\n" (print_bool_option res_simple) time_simple in
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let _ = printf "Abdallah' solver : %B in %fs\n" babdallah tabdallah in
  ()

let _ = start_simple()
