open Aez
open Asttypes
open Typed_ast

module Iota = Map.Make(Ident)
module Mu = Map.Make(String)
            
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
   
type formula =
  | Form of Smt.Formula.t
  | Term of Smt.Term.t
  | Nothing
          
type z_node =
  { z_name: Ident.t;
    node_input: (Ident.t * Asttypes.base_ty) list;
    node_output: (Ident.t * Asttypes.base_ty) list;
    node_vlocal: (Ident.t * Asttypes.base_ty) list;
    node_equs: (Smt.Term.t -> Aez.Smt.Formula.t) list;
    node_loc: location;
    mutable symboles: Hstring.t Iota.t;
  }
  
type map_fun_env =
  {
    mutable fun_name : Ident.t list;  
    mutable form_arr: (formula list) array;
  }

let (<><>) a1 a2 =
  Array.append a1 a2
  
module M = Map.Make(Ident)
module Phy =
  struct
    type t = formula list M.t
    let empty = M.empty
              
    let init key env =
      M.add key []
      
    let add key f env =
      if M.mem key env then
        let ll = (M.find key env) in
        M.add key (ll @ [f]) env
      else 
        M.add key [f] env
      
    let find key env =      
      try
        M.find key env
      with
      | Not_found -> raise Not_found
  end
