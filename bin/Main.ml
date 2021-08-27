(*open Printf*)
module D = Dlpag
open Mctsdlpag
open Core
open Core_bench
module S = Stdlib.Sys

let verbose = ref false

exception Exit of float

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
  let t = S.time() in
  let fx = f x  in fx, S.time() -. t

let avg_time n b f x =
  let fs = ref 0. in
  for i = 1 to (n-1) do (
    let _, t = time f x in
    fs := !fs +. t;
    if b then printf "avg:%fs \t now :%fs\n" (!fs/.(float_of_int i)) t;
  )
  done;
  let fx, tfinal = time f x in
  fx, (!fs+.tfinal)/.((float_of_int n))

let bench n f x =
  let fs = ref 0. in
  try
  for _ = 1 to (n) do (
    let (fx,_) , t = time f x in(
    match fx with
    None -> printf "None result : "; raise (Exit(t))
  | _ -> ()
    );
    fs := !fs +. t;
  )
  done;
  (!fs)/.((float_of_int n))
  with Exit(t) -> t

let get_formula () = 
  let f = get_filename () in
  let p = D.Parse.from_file () f in
  (*printf "%s\n\n" (D.Ast.Print.file p);*)
  let g = D.Circuit.file p in
  g, D.Formula.file g

let print_bool_option = function
  | None -> sprintf "NONE"
  | Some b -> sprintf "%B" b

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
  let res_simple, time_simple = avg_time 1 false Simple.solve new_f in 
  let babdallah, tabdallah = time (D.Solve.model_checking dcircuit) [] in
  let treeN =  100000 in
  let (res_mcdsv2, _), time_mcdsv2 = avg_time 1 false (MCDSv2.solve new_f) treeN in 
  let _= printf "Simple : %s in %fs\n" (print_bool_option res_simple) time_simple in
  let _= printf "MCDSv2 : %s in %fs\n" (print_bool_option res_mcdsv2) time_mcdsv2 in
  let _ = printf "Abdallah' solver : %B in %fs\n" babdallah tabdallah in
  ()

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
let name_to_formula name =
  let p = D.Parse.from_file () name in
  (*printf "%s\n\n" (D.Ast.Print.file p);*)
  let g = D.Circuit.file p in
  Formula.formula_retread (D.Formula.file g)

let start_corebench() =
  let _ = Random.self_init() in
  let _ = "tests.t/ut_star.pa"(*; "tests.t/ut_star_cmplx.pa"] in*) in
  let f = "encodings/hanoi.pa" in
  let f = name_to_formula f  in
  let bign = 10000000 in
  Command.run (Bench.make_command [
    Bench.Test.create
    ~name:"simple" 
        (fun () -> ignore (Simple.solve f));
    Bench.Test.create
    ~name:"notmodal" 
        (fun () -> ignore (MCDS_notmodal.solve f bign));
    Bench.Test.create
    ~name:"allbutkleene" 
        (fun () -> ignore (MCDS_allbutkleene.solve f bign));
    Bench.Test.create
    ~name:"deteronly" 
        (fun () -> ignore (MCDS_deteronly.solve f bign));
    Bench.Test.create
    ~name:"size" 
        (fun () -> ignore (MCDS_size.solve f bign));
(*    Bench.Test.create
    ~name:"MCDS no oracle" 
        (fun () -> ignore (MCDSv2.solve f bign)); *)
  ])
  (*
  Command.run (Bench.make_command [
    Bench.Test.create ~name "notmodal"
    (fun () -> ());
    (*(fun () -> ignore(MCDS_notmodal.solve new_f 10000));*)
    Bench.Test.create ~name "allbutkleene"
    (fun () -> MCDS_allbutkleene.solve new_f 10000);
  ]) *)
let () = start_corebench()
