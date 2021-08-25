open Printf

type t = { was_tried : int;
  reward : int;
  to_prove : int; (* decrease when a false is found for OR *)
}
let init n = {was_tried = 0; reward =0; to_prove=n}

module Print = struct
  let statistics s = sprintf "{was_tried=%d; reward=%d; to_prove=%d}" s.was_tried s.reward s.to_prove
end
