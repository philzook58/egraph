

type disjoint_set = {
  parents : int Vector.t
}

let init : disjoint_set = {
  parents = Vector.make 0 ~dummy:-1
}

(*
https://discuss.ocaml.org/t/adding-dynamic-arrays-vectors-to-stdlib/4697/7
dynamics arrays
*)
let push (ds : disjoint_set) : unit =
  Vector.push ds.parents -1

let find_root (ds : disjoint_set) i : int =
  let pi = Vector.unsafe_get i in
  if (pi < 0) then pi else find_root ds pi

  (* while (Vector.unsafe_get i > 0) do
    
  done *)

let union (ds : disjoint_set) (i j : int) : int =
  let pi = find_root ds i in
  let pj = find_root ds j in
  if pi = pj then
    pj
  else
    let pi, pj = if pj < pi then (pi, pj) else (pj, pi) in
    Vector.set pj (pj + pi);
    Vector.set pi pj;
    pj





(*
alt-ergo union find
https://github.com/OCamlPro/alt-ergo/blob/next/src/lib/reasoners/uf.mli
*)



