open Printf
let _ = ignore (sprintf "")

module D = Dlpag

(* naming decided by type, SS = string set, SSS = string set set, not great if we might change data structure *)
module SS = Set.Make (struct type t = string let compare = compare end)
module SSS = Set.Make (struct type t = SS.t let compare = SS.compare end)

type foperator = Conj | Disj 
type poperator = Seq | U
type formula = Base of bool | Var of (bool * string) | ListF of (foperator * formula list) | Modal of (bool * program * formula)
and program = Assign of string * formula | Kleene of program | Test of formula | ListP of (poperator * program list)

module Print = struct
  let list' ll sep rr funl l = sprintf "%s%s%s" ll (String.concat sep (List.map funl l)) rr
  let list funl = list' "[" ";" "]" funl
  let rec formula = function
    | Base true -> "T"
    | Base false -> "F"
    | Var (b, s) -> sprintf "%s%s" ((function true -> "" | false -> "\\neg ") b) s
    | ListF(fop, lf) ->  (list' "" (sprintf " %s " (foperator fop)) "" formula lf)
    | Modal(diam, p, f) ->
      if diam then sprintf "<%s>(%s)" (program p) (formula f)
      else         sprintf "[%s](%s)" (program p) (formula f)
  and program = function
    | Assign(s, f) -> sprintf "(%s <- %s)" s (formula f)
    | Kleene p -> sprintf "%s*" (program p)
    | Test f -> sprintf "?%s?" (formula f)
    | ListP(pop, lp) -> sprintf "(%s)" (list' "" (sprintf " %s " (poperator pop)) "" program lp)
  and foperator = function
    | Conj -> "^"
    | Disj -> "v"
  and poperator = function
    | Seq -> ";"
    | U -> "U"
  let ss' ld id rd l = 
    (*| l when SS.cardinal l = 0-> ""*)
    sprintf "%s%s%s" ld (String.concat id (SS.elements l)) rd
  let ss set = ss' "{" "," "}" set
  let sss' ld id rd (set:SSS.t) = 
    sprintf "%s%s%s" ld (String.concat id (List.map ss (SSS.elements set))) rd
  let sss (set:SSS.t) = sss' "{" ", " "}" set

end

(*** Converting Dlpag's formula to our formula type *)
(*** current changes : Circuit.callable -> string *)
let rec formula_retread (old_f:D.Formula.formula) = match old_f with
  | D.Formula.CallF(b, callable) -> Var(b, D.Circuit.Print.callable callable)
  | D.Formula.Base b -> Base b
  | D.Formula.ListF(old_fop, old_lf) -> ListF(fop_retread old_fop, List.map formula_retread old_lf)
  | D.Formula.Modal(diam, old_p, old_phi) -> Modal(diam, program_retread old_p, formula_retread old_phi)

and program_retread (old_p:D.Formula.program) = match old_p with
  | D.Formula.Test old_psi -> let new_psi = formula_retread old_psi in Test new_psi
  | D.Formula.ListP(old_pop, old_lp) -> ListP(pop_retread old_pop, List.map program_retread old_lp)
  | D.Formula.Assign(callable, old_psi) -> Assign(D.Circuit.Print.callable callable, formula_retread old_psi)
  | D.Formula.Kleene old_p -> Kleene(program_retread old_p)
  | D.Formula.Converse _ -> failwith "Not implemented"
and fop_retread = function
  | D.Ast.T.Conj -> Conj
  | D.Ast.T.Disj -> Disj
and pop_retread = function
  | D.Ast.T.Seq -> Seq
  | D.Ast.T.U -> U
