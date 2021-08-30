open Statistics
open Printf
let _ = ignore (sprintf "")

let uCB ntotal n nwin constant = 
  (*let _ = printf "ntotal : %d, n:%d, nwin :%d , constant :%f\n" ntotal n nwin constant in*)
  let ntotal, n= float_of_int ntotal, float_of_int n in
  nwin/.n +. constant *. sqrt(log(ntotal)/.n)

let compute_score s_parents s_child nop constant = 
  match nop with
  | Node.And -> uCB s_parents.was_tried s_child.was_tried ((float_of_int s_child.was_tried) -. s_child.reward) constant
  | Node.Or -> uCB s_parents.was_tried s_child.was_tried s_child.reward constant
  | Node.Not -> 1.0
  (*TODO try stuff*)


let update_res { was_tried = i; reward = ri ; to_prove = n} nop play_res boolnode = 
  let resint, tries = match play_res,nop with
    | None,_ -> 0., 0
    | Some true, Node.Not -> 0., 1
    | Some false, Node.Not -> 1., 1
    | Some true, _ -> 1., 1
    | Some false, _ -> 0., 1
  in let to_prove =
    match boolnode,nop with
    | Some true, Node.And -> n-1 
    | Some false, Node.Or -> n-1
    | _, _ -> n
  in let newbool = match to_prove, nop, boolnode with
    | _, Node.And, Some false -> Some false
    | _, Node.Or , Some true -> Some true
    | _, Node.Not, Some b -> Some (not b)
    | 0, Node.And,_ -> Some true
    | 0, Node.Or,_ -> Some false
    | _ -> None
  in newbool, {was_tried = i+tries; reward = ri+.resint; to_prove=to_prove}


let update_res_n { was_tried = i; reward = ri ; to_prove = n} nop play_res boolnode nplayout = 
  let resint, tries = match play_res, nop with
    | None, _ -> 0.,0
    | Some x, Node.Not -> (1.-.x),nplayout
    | Some x, _ -> x,nplayout
  in let to_prove =
    match boolnode,nop with
    | Some true, Node.And -> n-1 
    | Some false, Node.Or -> n-1
    | _, _ -> n
  in let newbool = match to_prove, nop, boolnode with
    | _, Node.And, Some false -> Some false
    | _, Node.Or , Some true -> Some true
    | _, Node.Not, Some b -> Some (not b)
    | 0, Node.And,_ -> Some true
    | 0, Node.Or,_ -> Some false
    | _ -> None
  in newbool, {was_tried = i+tries; reward = ri+.resint; to_prove=to_prove}
