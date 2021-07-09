open Core_kernel
(* this file is part of datalog. See README for the license *)

(** {1 AST for TopDown terms} *)

type term =
  | Var of string
  | Apply of string * term list
  | Int of int [@@deriving sexp]


let pp_list_comma pp_v = Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_text ppf ",") pp_v

let rec pp_term ppf term =  
  match term with
  | Var v -> Format.fprintf ppf "%s" v
  | Apply (f, []) -> Format.fprintf ppf "%s" f
  | Apply ("=", [a ; b]) -> Format.fprintf ppf "%a = %a" pp_term a pp_term b
  | Apply (f, args) -> Format.fprintf ppf "%s(%a)" f (pp_list_comma pp_term)  args
  | Int i -> Format.fprintf ppf "%d" i 

let print_term = pp_term Format.std_formatter


type aggregate = {
  ag_left : term;
  ag_constructor : string;
  ag_var : string;
  ag_guard : term;
} (* aggregate: ag_left = ag_constructor set
    where set is the set of bindings to ag_var
    that satisfy ag_guard *) [@@deriving sexp]

type literal =
  | LitPos of term
  | LitNeg of term
  | LitAggr of aggregate [@@deriving sexp]

let pp_literal ppf lit =  
  match lit with
  | LitPos t -> Format.fprintf ppf "%a" pp_term t
  | LitNeg t -> Format.fprintf ppf "!%a" pp_term t
  | _ -> failwith "no printing of aggregate"

type clause = term * literal list [@@deriving sexp]

let pp_clause ppf (head, body) = 
  Format.fprintf ppf "%a :- %a." pp_term head (pp_list_comma pp_literal) body

let print_clause = pp_clause Format.std_formatter
type file = clause list

let pp_file = 
  Format.pp_print_list ~pp_sep:Format.pp_print_newline pp_clause

let print_file = pp_file Format.std_formatter

exception ParseError of string

let loc_to_str pos =
  Printf.sprintf "line %d, column %d"
    pos.Lexing.pos_lnum
    (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)

let print_error ?(out=stderr) msg lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let stop = Lexing.lexeme_end_p lexbuf in
  Printf.fprintf out "parse error between %s and %s: %s\n"
    (loc_to_str start) (loc_to_str stop) msg

let error_to_string msg lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let stop = Lexing.lexeme_end_p lexbuf in
  Printf.sprintf "parse error between %s and %s: %s\n"
    (loc_to_str start) (loc_to_str stop) msg