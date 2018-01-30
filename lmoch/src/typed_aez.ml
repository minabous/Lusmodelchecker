type constant = Asttypes.const
              
type term_op = Op_plus |  Op_minus | Op_times |  Op_div | Op_mod

type comparison = Cmp_eq | Cmp_neq | Cmp_lt | Cmp_leq

type combinator = Cmb_and |Cmb_or | Cmb_impl | Cmb_not

type ident = Ident.t

type term =
  | T_cst of constant
  | T_op of term_op * term * term
  | T_ite of formule * term * term
  | T_formule of formule
  | T_app of ident * int
and formule =
  | F_term of term
  | F_cmp of comparison * term * term
  | F_lco of combinator * (formule list)
  | F_app of term list


           (*
type stream_body = SB_term of term | SB_formula of formula

type stream_declaration = { 
  sd_ident: ident;
  sd_type: Asttypes.base_ty;
  sd_body: stream_body
}

            *)

(* type node = stream_declaration list *)
type node =
  { node_name: ident;
    node_input: (Aez.Hstring.t * Asttypes.base_ty) list;
    node_output: (Aez.Hstring.t * Asttypes.base_ty) list;
    node_vlocal: (Aez.Hstring.t * Asttypes.base_ty) list;
    node_equs: ( int -> Aez.Smt.Formula.t) list;
    node_loc: Asttypes.location;
  }
