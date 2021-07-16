open Core_kernel
open AST

(*
gensyms for generating new names
*)

let gensym = let counter = ref 0 in
             fun () -> incr counter; AST.Var (Printf.sprintf "Gvar%d" !counter)
let genterm = let counter = ref 0 in
              fun () -> incr counter;
                let tname = (Printf.sprintf "genrel%d" !counter) in
                fun args -> AST.Apply (tname, args)
(* stage allows us to stage a single datalog file *)
let stage = ref 0


let rec is_ground (* grounded : String.Set.t *)(t : AST.term) =
  match t with 
   | Var _ -> false
   | Apply (_, args) -> List.for_all ~f:is_ground args
   | Int _ -> true

(** collect up all variables in a term *)
let rec all_vars t = 
  match t with 
  | Var v -> [v]
  | Int _ -> []
  | Apply (_, args) -> List.concat_map ~f:all_vars args

let term_of_lit l = match l with
 | LitPos t -> t
 | _ -> failwith "unexpected literal"

let equiv_decl = ".decl equiv(n : number, m:number) eqrel\n"
let equiv a b = AST.Apply ("equiv", [a; b]) 

(* Dollar increments a gensym counter at datalog runtime *)
let dollar : AST.term = Apply ("$", [])

let rec gensyms n = if n > 0 then gensym () :: (gensyms (n-1)) else []
let sum l = List.fold ~init:0 ~f:(fun a b -> a + b) l
let rec term_count t = match t with
 | Apply (_, args) -> sum (List.map ~f:term_count args)
 | _ -> 0
let rec repeat n x = if n > 0 then x :: (repeat (n-1) x) else []

let litpos b = List.map ~f:(fun t -> LitPos t) b

let last l = List.hd_exn (List.rev l)

let last_arg t = 
 match t with
  | Apply (_f, args) -> last args
  | _ -> failwith "lastarg bad argument"

(* collect up all the symbols and arity's in a term *)
let symarity (t : term) : (string * int) list =
  let rec worker t = 
  match t with
  | Apply (f, args) -> (f , List.length args) :: List.concat_map ~f:worker args
  | _ -> []
  in
  List.dedup_and_sort ~compare:[%compare: string * int] (worker t)


(** 
Build a congurence closure axiom of the form
equiv(r1,r2) :- f(a,b,c,...,r1), equiv(a,a1), aquiv(b,b1), equiv, f(a1,b2,c1,...,r2)
 *)
let congruence (head, arity) : AST.clause = 
   let args1 = gensyms arity in
   let args2 = gensyms arity in
   let equivs = List.map2_exn ~f:(fun a b -> equiv a b) args1 args2 in
   let res1 = gensym () in
   let res2 = gensym () in
   let t1 = Apply (head, args1 @ [res1]) in
   let t2 = Apply (head, args2 @ [res2]) in
   equiv res1 res2, litpos ((t1 :: equivs) @ [t2])


(*  let rec (grounded : )*)

(** 
[flat_term] take a functional term and flattens it into relational form using generated variables.
Useful for the right hand side of rules.
 *)
let rec flat_term (t : AST.term) : AST.term * AST.term list =
  (* if is_ground t then  *)
  match t with
  | Var v -> Var ("v"  ^ v), []
  | Apply (f, args) ->
      let (args1, subterms) = List.map ~f:flat_term args |> List.unzip in
      let subterms = List.concat subterms in
      let args2 = List.map args ~f:(fun a -> 
        match a with
        | Int _ -> a
        | _ -> gensym ())
        (* Do i expand the Var using quiv or not? Depends on the normalization of my relations I think *)
       (* ~f:(fun _ -> gensym ()) *) (* ~f:(fun a -> 
        match a with
        | Apply (_, _) -> gensym ()
        | Var v -> Var ("v" ^ v)
        | Int _ -> a) *)
      in
      (* index of current term *)
      let i = gensym () in
      let equivs = List.map2_exn ~f:(fun a b -> equiv a b) args1 args2 in
            (* 
            TODO: should I change ordering of query depending on if ground or not?
            let terms = if is_ground t then subterms @ equivs @ AST.Apply *)
      i , AST.Apply (f, args2 @ [i]) :: equivs @ subterms
  | Int i ->  Int i, [] (* failwith? *)

(** Expand an equality into quiv and then flattens *)
let eq_flat_term t = 
  match t with
  | Apply ("=", [a ; b]) -> let i, tas = flat_term a in
                            let j, tbs = flat_term b in
                            tas @ (equiv i j :: tbs)
  | _ -> let (_, ts) = flat_term t in ts

(* Generate pattern found predicate

 *)


(**
heads flatten differently because we don't need the equivs between them
 *)

let rec flat_head (t : AST.term) : AST.term * AST.term list =
  match t with
  | Var v -> Var ("v"  ^ v), []
  | Apply (f, args) ->
      let (args1, subterms) = List.map ~f:flat_head args |> List.unzip in
      let subterms = List.concat subterms in
      let i = gensym () in
      i , AST.Apply (f, args1 @ [i]) :: subterms
  | Int i ->  Int i, [] 


(** [compile_clause] converts a clause into the pattern finder and instantiater that clause corresponds to *)

let compile_clause ((head,body) : AST.clause) : AST.clause list =
  let head_vars = List.map ~f:(fun v -> Var v) (all_vars head) in
  let (_, flat_head) = flat_head head in (* TODO: is the head an eq or no? *)
  let dollars = repeat (List.length flat_head) dollar in
  let aux_term = genterm () in (* Holds found pattern *)
  let aux_head = aux_term (dollars @ head_vars) in (* with dollars gensyms *)
  (* eq_flat_term head *)
  let body = List.concat_map ~f:(fun x -> eq_flat_term (term_of_lit x)) body in 
  (* clause that actually finds pattern *)
  let pat_finder = (aux_head , litpos body) in
  
  let aux_vars = List.map ~f:last_arg flat_head in
  let aux_body = litpos [aux_term ( aux_vars  @ head_vars)] in
  let instans : clause list = List.map ~f:(fun h -> (h, aux_body)) flat_head in
  pat_finder :: instans 





let term_of_string s : Lexing.lexbuf =
  let lexbuf = Lexing.from_string s in lexbuf


let ex = "foo(g(A,x)) = biz(Z) :- bar(b)."
(*let _ = term_of_string ex *)

let parse_clause (s : string) : AST.clause = 
  let lexbuf = Lexing.from_string s in
  let ast = Parser.parse_clause Lexer.token lexbuf in
  ast

let lexbuf = Lexing.from_string ex

let ast = Parser.parse_clause Lexer.token lexbuf 
let () =  ast |> AST.sexp_of_clause |> Sexp.to_string |> print_endline
let () = AST.print_term (fst ast)
let () = Format.print_newline ()
let () = AST.print_clause ast

let () = Format.print_newline ()
(* let () = AST.print_clause (compile ex) *)

let _ex = "biz(Z) :- bar(b) = foo(Z,h(q))."
let () = Format.print_newline ()

let ex = "biz(Z) :- bar(b) = foo(Z,h(q))."
let ast = parse_clause ex

let () = AST.print_clause ast
let () = Format.print_newline ()
let () = List.iter ~f:AST.print_clause (flat_clause ast)
let () = Format.print_newline ()


(*
I could make an intermidate preciate
gen(a,b,c,namedvars,  $,$,$,$,$).
f(a,b,gen3) :- gen(   , gen3, ...).

Hard / impossible to suppress creation of variables.
This is obviously pretty bad. Puts pressure on the duplicate cleanup

We're getting a lot of n^2

Maybe I should make my ocaml / metaocaml egraph

I want to output comments too btw.
I kind of want to read comments too
A comment that describes the original input expression this derived from

*)
(*
We may want to order leaves first if ground

Are the ids eclass ids or enode ids?
Do I want to have them be unique?

If I don't normalize, I have as much searching up as i do down.
If I know unique, I can remove equiv() indirection.

We could have a staged set of intermediate repdicates making $


*)
(*
let oc = Caml.Unix.open_process_out "souffle --help"
let () = print_string (input_line oc)
let status = Unix.close_process_out oc

let table = Csv.load "testfile.csv"

let rec pp_sexp_of_term ppf t =
  match t with 
  | Apply ("f", args) -> Format.fprintf ppf "(%s %a)" f (pp_list ~sep:space pp_sexp_of_term) args
  | Var j -> Format.fprintf ppf "?%s" j
  | Int i -> Format.fprintf ppf "%d" i

let pp_egg_check ppf t =
  match t with
  | Apply "=" [a;b] -> Format.fprintf ppf "ConditionEq(\"%a\",\"%a\")" pp_sexp_of_term a pp_sexp_of_term b
  | _ -> failwith "expected toplevel equal in body" 

let pp_egg_clause ppf (head,body) = 
  match head with
  | Apply "=" [a;b] -> Format.fprintf "rw!(\"%a\",\"%a\" )" pp_sexp_of_term a pp_sexp_of_term b (list pp_egg_check) body
  | _ -> failwith "expected toplevel equal in head";
  match body with
  | [] -> ()
  | _ -> 


(*
Direct datalog control flow
pat(A,X,Y) :- 
  :- pat(),   f(X,Y,Z)
 $ :-  pat(), !f(X,Y,_)
Minimal egraph just for hashcons lookup. already rnoamlized

We just need to read in and generate.
Just allow all new variables and count on congruence closure mechanism.

If we generate, we could 
pat($$$$) :- 
f(X,Y,A) :- pat(A), !f(x,Y,_)
equiv(Z,A) :- pat(A), f(x,Y,Z) // immediately finds the congurence closure. Avoids adding f(X,Y,A)

pattern search
instantiate
congruence
minimize -- not necesary
repeat

We lose the smart delta properties.

type era_term = int * term





*)
( ) String.Map,t

type enode = {
  head : string (* intern? *)
  args : eclass elem (* int list *)
} 

(*
type enode = {
  head : string (* intern? *)
  args : eclass elem (* int list *)
} 
type eclassid = int
type eclass = ref (enode list)
type egraph = {
  root : eclassid Int.Map.t;
  memo : eclassid ENode.Map.t;
  eclasses : eclass Int.Map.t
}
module EGraph = struct
 
 include UnionFindBasic with 'a := eclass
 let join ec1 ec2 = let e1 = ec1
 let union a b =
   let x = get a in
   let y = get b in
   let join x y in
   union a b
end
*)
module UF = UnionFind.Make(UnionFind.StoreVector)

module EClass = 
struct
include UnionFind.Make(UnionFind.StoreVector)
let union (x : eclass rref) (y : eclass rref) = union ENode.Set.union x y
(* this gets us the union find map
   
 *)
end


let eclass_union = UF.union ENode.Set.union 
*)



(* type ground_term =  *)
(*
type term = {head : string; args : term list}
type obj = IVar of int | ILit of int | SVar of string | SLit of string 
type rel = Eq of term * term | Rel of {name : string ; args : obj list}
type clause = {head : rel; body : rel list}
type prog = clause list

let gensym = let counter = ref 0 in
             fun () -> incr counter; !counter
*)
             (*
let rec flatterm (t : term) : int * rel list =
  let iargs, rels = List.split (flatterm t.args) in
  let i = gensym () in
  let args = List.map (fun j -> IVar j) iargs in
  i, {name = t.head; args = iargs ++ [IVar i]} :: rels

let rec symarity (t : term) : (string * int) list =
  (t.head , List.length t.args) :: List.concatmap ~f:symarity t.args

*)