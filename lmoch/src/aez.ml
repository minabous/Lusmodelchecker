type constant =Asttypes.const


type term_op= Op_plus |  Op_minus | Op_times |  Op_div |  Op_mod

type comparison = Cmp_eq | Cmp_neq | Cmp_lt | Cmp_leq

type combinator = Cmb_and |Cmb_or | Cmb_impl | Cmb_not

type ident = Ident.t


type term =
  | T_cst of constant
  | T_op of term_operator * term * term
  | T_ite of formula * term * term
  | T_formula of formul

type formul=
  || F_term of term
  | F_cmp of comparison * term * term
  | F_lco of logic_connector * (formula list)


type stream_body = SB_term of term | SB_formula of formula

type stream_declaration = { 
  sd_ident: ident;
  sd_type: Asttypes.base_ty;
  sd_body: stream_body
}


type node = stream_declaration list
