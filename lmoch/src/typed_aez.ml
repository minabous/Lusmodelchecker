open Aez
open Asttypes
open Typed_ast

module Iota = Map.Make(Ident)

type z_var = Ident.t * base_ty
               
type operateur =
  | Calculator of op
  | Comparator of op
  | Combinator of op
  | Branchment of op

type constante = Asttypes.const

type z_expr =
  { zexpr_desc: z_expr_desc;
    zexpr_type:  ty;
  } 
           
and z_expr_desc =
  | Z_const of const
  | Z_ident of Ident.t
  | Z_op of operateur * z_expr list
  | Z_app of Ident.t * z_expr list
  | Z_prim of Ident.t * z_expr list
  | Z_arrow of z_expr * z_expr
  | Z_pre of z_expr
  | Z_tuple of z_expr list

             
type z_equation =
  { zeq_patt: t_patt;
    zeq_expr: z_expr; }
   

type z_node =
  { z_name: Ident.t;
    node_input: (Ident.t * Asttypes.base_ty) list;
    node_output: (Ident.t * Asttypes.base_ty) list;
    node_vlocal: (Ident.t * Asttypes.base_ty) list;
    node_equs: (Smt.Term.t -> Aez.Smt.Formula.t) list;
    node_loc: location;
    mutable symboles: Hstring.t Iota.t;
  }
