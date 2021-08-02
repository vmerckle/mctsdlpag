open Printf
open Dlpag

let update reference value = reference := value
let get () =
  let speclist = [] in
  let usage_msg = "DL-PA Grounder. Options available:" in
  let input_names = ref [] in
  let add_name s = input_names := s :: !input_names in
  Arg.parse speclist add_name usage_msg;
  match !input_names with
  | n :: [] -> n
  | _ :: _ :: _ | [] -> failwith "Wrong number of arguments. Usage: dlpag file"

let time f x =
  let t = Sys.time() in
  let fx = f x  in fx, Sys.time() -. t

let start () =
  let _ = Random.self_init() in 
  let f = get () in
  let p = Parse.from_file () f in
  (*printf "%s\n\n" (Ast.Print.file p);*)
  let g = Circuit.file p in
  let f = Formula.file g in
  let fi = MCTSutils.formToIForm f in 
  let tree = MCTSutils.splitIF (MCTSutils.SS.empty) fi in
  let _= printf "\nInput formula : %s \n" (Formula.Print.formula f) in 
  let _= printf "it has %d variables.\n\n" (MCTSutils.acountF f) in
  let _= printf "Internal formula : %s \n" (MCTSutils.Print.iformula fi) in 
  let _= printf "After one split : \n%s\nPlaythrough now\n\n" (MCTSutils.Print.arbre tree) in
  let babdallah, tabdallah = time (Solve.model_checking g) [] in
  let bbrute, tbrute = if true then time (MCTSutils.playthrough tree false) 0 else true,0. in
  let nodecount = (* MCTSutils.playthroughcount tree 0 *) 0  in (* very slow *)
  let _,y = if true then MCTSutils.playthroughc tree else false,0 in
  let  nn = 2000000 in
  let (bdag, dcount), tdag = time (Vache.solve fi) nn in let _= match bdag with
    MCTSutils.Proven b -> printf "\n%B : DAG. in %d steps\n" b dcount
  | MCTSutils.Ni -> printf " \nNo answer : DAG. in %d steps\n" dcount
  in 
  let (bmcts,count), tmcts = time (MCTS.solve fi) nn in let _= match bmcts with
    MCTSutils.Proven b -> printf "%B : MCTS. in %d steps\n" b count
  | MCTSutils.Ni -> printf " No answer : MCTS. in %d steps\n" count
  in
  let _= printf "%B : Abdallah's naive solver found\n" babdallah in
  let _ = printf "%B : Brute playthrough in %d steps out of %d total nodes\n" bbrute y nodecount in 
  ignore (printf "Abdallah : %fs, Brute : %fs, Mcts : %fs, Dag : %fs\n" tabdallah tbrute tmcts tdag)

let _ = start ()
