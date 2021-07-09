open Core_kernel
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
open AST
let gensym = let counter = ref 0 in
             fun () -> incr counter; AST.Var (Printf.sprintf "Gvar%d" !counter)
let genterm = let counter = ref 0 in
              fun () -> incr counter;
                let tname = (Printf.sprintf "genrel%d" !counter) in
                fun args -> AST.Apply (tname, args)

let equiv a b = AST.Apply ("equiv", [a; b])   

let term_of_lit l = match l with
 | LitPos t -> t
 | _ -> failwith "unexpected literal"

 
let rec is_ground (* grounded : String.Set.t *)(t : AST.term) =
  match t with 
   | Var _ -> false
   | Apply (_, args) -> List.for_all ~f:is_ground args
   | Int _ -> true
(*
We may want to order leaves first if ground

Are the ids eclass ids or enode ids?
Do I want to have them be unique?

If I don't normalize, I have as much searching up as i do down.
If I know unique, I can remove equiv() indirection.

We could have a staged set of intermediate repdicates making $


*)

(*  let rec (grounded : )*)
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
      let i = gensym () in
      let equivs = List.map2_exn ~f:(fun a b -> equiv a b) args1 args2 in
            (* let terms = if is_ground t then subterms @ equivs @ AST.Apply *)
      i , AST.Apply (f, args2 @ [i]) :: equivs @ subterms
  | Int i ->  Int i, [] (* failwith? *)

let eq_flat_term t = 
  match t with
  | Apply ("=", [a ; b]) -> let i, tas = flat_term a in
                            let j, tbs = flat_term b in
                            tas @ (equiv i j :: tbs)
  | _ -> let (_, ts) = flat_term t in ts

let rec all_vars t = 
  match t with 
  | Var v -> [v]
  | Int _ -> []
  | Apply (_, args) -> List.concat_map ~f:all_vars args

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

let flat_clause ((head,body) : AST.clause) : AST.clause =
  let head_vars = List.map ~f:(fun v -> Var v) (all_vars head) in
  let aux_head = genterm () head_vars in
  (* eq_flat_term head *)
  let body = List.concat_map ~f:(fun x -> eq_flat_term (term_of_lit x)) body in
  let body = List.map ~f:(fun c -> LitPos c) body in 
  (aux_head , body)


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
let () = AST.print_clause (flat_clause ast)
let () = Format.print_newline ()

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




