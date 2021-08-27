module Sys = Stdlib.Sys (* otherwise this doesn't work with bench *)
open Printf

exception Noneres of float

let time f x =
  let t = Sys.time() in
  let fx = f x  in fx, Sys.time() -. t

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
    None -> printf "None result : "; raise (Noneres(t))
  | _ -> ()
    );
    fs := !fs +. t;
  )
  done;
  (!fs)/.((float_of_int n))
  with Noneres(t) -> t
