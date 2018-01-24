open Aez
open Smt
open Num

(*
let input_to_aez input =
  match input with
  | (x, ty) -> (x, ty)
  | _ -> failwith "ast_to_aez::input_to_aez::Not a correct input"
     (*  | _ -> failwith "ast_to_aez::input_to_aez::Not Implemented" *)
 *)

module Iota = Map.Make(String)
type iota = Hstring.t Iota.t
let env = Iota.empty
        
let declare_symbol name t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  ignore (Iota.add name x env);
  x
   
let var_aez input =
  match input with
  | (x, ty) ->
     match ty with
     | Asttypes.Tbool -> declare_symbol x [Type.type_int] Type.type_bool
     | Asttypes.Tint  -> declare_symbol x [Type.type_int] Type.type_int
     | Asttypes.Treal -> declare_symbol x [Type.type_int] Type.type_real
     | _ -> failwith "ast_to_aez::var_aez::Unknown type\n Type Has to be int, bool float"


          
(* Eventuellement faire cette transformation 
 avant en créant un asttyped_aez pour ensuite parcourir une seul listes. *)
let create_couple_var_ty var ty =
  (var, ty)
  
(* Ici pour chaque Patt = expr, on renvoit une Formula
   afin de construire la liste des formules à prouver
 *)
  
let make_term exprl =
(*
  match exprl with
  | [] -> failwith "transform_aez::make_term:: No expression in list"
  | a::tl ->
     begin
     end
 *)
  match exprl with
  | Typed_ast.TE_const(c) ->
     match c with
     | Cbool(b) ->
        begin
          match b with
          | true  -> Term.t_true
          | false -> Term.t_false
        end
     | Cint(i) -> Term.make_int (Int i )
     (* | Creal(f) -> Term.make_real (Num.float_of_num f) *)
     | _ -> failwith "ast_to_aez::for_each_pattern_his_eq::Unknown constant type (only int are available yet)"
(*
  | Typed_ast.TE_ident(id) ->
     let vary = Iota.find id.name env in
     Term.make_app vary [n] *)
(*  Tout les expression qui contiennent des listes d'expressions :
      Faire après.
   *)
     (*
  | TE_op (op, el) ->
     begin
       match op with
       | Op_eq  ->
          begin
            match el with
            | [] | [a] ->
               failwith "transform_aez::
                         create_application::
                         Moins de deux opérandes 
                         pour un opérateur egal ??"
            | e :: tl ->
               Term.make_arith Plus (make_term [e]) (make_term tl)
          end
       | Op_neq ->
          
       | Op_lt  ->
       | Op_le  ->
       | Op_gt  ->
       | Op_ge  ->
          
       | Op_add ->
          begin
            match el with
            | [] | [a] ->
               failwith "transform_aez::
                         create_application::
                         Moins de deux opéarande 
                         pour un opérateur Plus ??"
            | e :: tl ->
               Term.make_arith Plus (make_term [e]) (make_term tl)
          end
       | Op_sub ->
                      | [] | [a] ->
               failwith "transform_aez::
                         create_application::
                         Moins de deux opéarande 
                         pour un opérateur Plus ??"
            | e :: tl ->
               Term.make_arith Plus (make_term [e]) (make_term tl)
          | Op_mul ->
          | Op_div ->
          | Op_mod ->
          | Op_add_f ->
          | Op_sub_f ->
          | Op_mul_f ->
          | Op_div_f ->
          | Op_not   ->
          | Op_and   ->
          | Op_or   ->
          | Op_impl ->
          | Op_if   ->
     end
   *)
     
let make_formula var expr =
  let varx = Iota.find var env in
  (fun n -> Formula.make_lit Formula.Eq
                 [ Term.make_app varx [n] ; make_term expr ])
  


(* Cette fonction créée la liste des formules pour construire
 le raisonnement kind par la suite. *)
let equs_aez equs =
  let vars = equs.teq_patt.tpatt_desc
  and tys = equs.teq_patt.tpatt_ty in
  let pattern = List.map2 create_tuple_var_ty vars tys in
  let expressions =
    match equs.teq_expr with
    | TE_tuple(el) -> el
    | _ -> [equs.teq_expr]
  in
  List.map2 make_formula pattern expressions
    
  
let ast_to_astaez texpr =
  let name =
    tnode.name in
  let input = (* DONE *)
    List.map var_aez texpr.tn_input in
  let output = (* DONE *)
    List.map var_aez texpr.tn_output in
  let local = (* DONE *)
    List.map var_aez texpr.tn_local in
  let equs = (* TODO *)
    List.map make_formula texpr.tn_equs in
  let loc = (* DONE *)
    texpr.tn_loc in
  { node_name = name;
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
    node_loc = loc;
  }



let compile_to_alt_ergo faez =
  failwith "ast_to_aez::compile_to_alt_ergo::Not Implemented"
  
let aezdify ast_node =
  let faez = List.map ast_to_astaez ast_node in
  Format.printf "End of aezidify \n";
  failwith "ast_to_aez::to_aez::Under Implementation"
   (* TODO *)



  (* Je pense avoir ce que patt signifie:
     dans le cas des equs:
     Une equation est un enregistrement de 
     { patt ,  pexpr }
     avec patt = 
     { PP_ident of ident (variable Seul) 
     | PP_tuple of ident list (Tuple)),
                location }
     avec pexpr = { p_expr_descr , location }
     p_expr_descr =
     | Constant
     | Ident
     | Op of op * pexpr list
     | ...(cf parse_ast.ml)

     Donc une équation c'est une affectation = une expression
     patt = pexpr
     Exemple:
     x = 5 * 2 + pre(z)

     Ici x = patt de type:
     { PP_ident(x), location }

     Et 5 * 2 + pre(z) = pexpr de la forme: 
     PE_op(PLUS, [PE_op(MUL, [5; 2]); PE_pre(PE_ident(z))]
     
     Autre exemple:
     (n1, n2) = (f -> pre(t), 6 * 7)

     ici (n1, n2) = patt de type:
     { PP_tuple([n1; n2]), location}

     Et (f->pre(t), 6 * 7) = pexpr de la forme
     PE_tuple ([PE_arrow(f, PE_pre(t)); 
                PE_op(MUL, [PE_const(Cint(6)); PE_const(Cint(7))])
                ])
     
     En espérant avoir éclairé un peu plus la compréhension du code
     Tu peux laisser des commentaires des suggestions etc.
   *)
