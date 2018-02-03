open Typed_aez
open Aez
open Smt
open Num
open Format
(*
let input_to_aez input =
  match input with
  | (x, ty) -> (x, ty)
  | _ -> failwith "ast_to_aez::input_to_aez::Not a correct input"
     (*  | _ -> failwith "ast_to_aez::input_to_aez::Not Implemented" *)
 *)

module Iota = Map.Make(String)

type iota =
  { mutable env: Aez.Hstring.t Iota.t; }

let symboles = { env=Iota.empty; }
             
let declare_symbol name t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  symboles.env <- Iota.add name x symboles.env;
  Printf.printf ", %s)\n" (Hstring.view x);
  x
   
let var_aez (input : Ident.t * Asttypes.base_ty) =
  match input with
  | (v, ty) ->
     Printf.printf "Nom des variables+Hstring : (%s" v.name;
     match ty with
     | Asttypes.Tbool -> (declare_symbol v.name [Type.type_int] Type.type_bool, ty)
     | Asttypes.Tint  -> (declare_symbol v.name [Type.type_int] Type.type_int, ty)
     | Asttypes.Treal -> (declare_symbol v.name [Type.type_int] Type.type_real, ty)
     | _ -> failwith "transform_aez::var_aez::Unknown type\n Type Has to be int, bool float"

  
(* Ici pour chaque Patt = expr, on renvoit une Formula
   afin de construire la liste des formules à prouver
 *)

let rec make_term expr =
  match expr with
  | Asttypes.Cbool(b) -> 
     begin
       match b with
       | true  -> Term.t_true
       | false -> Term.t_false
     end
  | Asttypes.Cint(i) ->  Term.make_int (Int i)
  | Asttypes.Creal(f) -> Term.make_real (Num.num_of_string (string_of_float f))
  | _ -> failwith "transform_aez::make_term::Unknown constant type (only int are available yet)"
          
  
and make_formula sym (expr: Typed_ast.t_expr_desc) (n: int) =
  match expr with
  | Typed_ast.TE_const(c) ->
     Formula.make_lit Formula.Eq
       [ Term.make_app sym [Term.make_int (Num.Int n)] ; make_term c ]      
  | Typed_ast.TE_ident(id) ->
     let var = Iota.find id.name symboles.env in
     Formula.make_lit Formula.Eq
       [ Term.make_app sym [Term.make_int (Num.Int n)];
         Term.make_app var [Term.make_int (Num.Int n)] ]
  | Typed_ast.TE_op (op, el) ->
       match op with
       | Op_add ->
          begin
            match el with
            | _ ->
               failwith "transform_aez::
                         create_application::
                         Moins de deux opéarande 
                         pour un opérateur Plus ??"
            | e1 :: e2 :: [] ->
               Term.make_arith Term.Plus (make_term e1 n) (make_term e2 n)
          end
       (*
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
        *)
          (*
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
  
          | Op_not   ->
          | Op_and   ->
          | Op_or   ->
          | Op_impl ->
          | Op_if   ->
     end
   *)

(* Eventuellement faire cette transformation 
 avant en créant un asttyped_aez pour ensuite parcourir une seul listes. *)
let create_couple_var_ty (var:Ident.t) (ty: Asttypes.base_ty) =
  (Iota.find_opt var.name symboles.env, ty)

  
let build_formula (varty: Aez.Smt.Symbol.t option * Asttypes.base_ty) (expr: Typed_ast.t_expr) =
  let var_symbol =
    match (fst varty) with
    | Some a -> a
    | None -> failwith "transform_aez::make_formula::Variable jamais declarer."
  in
  (fun n -> make_formula var_symbol expr.texpr_desc n)
  

(* Cette fonction créée la liste des formules pour construire
 le raisonnement kind par la suite. *)
let equs_aez (equs: Typed_ast.t_equation) =
  let vars = equs.teq_patt.tpatt_desc in
  let tys = equs.teq_patt.tpatt_type in
  let patterns = List.map2 create_couple_var_ty vars tys in
  let expressions =
    match equs.teq_expr.texpr_desc with
    | Typed_ast.TE_tuple(el) -> el
    | _ -> [equs.teq_expr]
  in

(**)
  List.map2 build_formula
    patterns
    expressions
    
  (* Note : equs = liste des equations.
   chaque equations est de la forme:
   (v, ..., vn) = expr, ..., exprn
   Le but est de transformer chaque formule par :
   v1 = expr1;
   ...
   vn = exprn;
   Donc equs_aez retourne la liste de toutes les égalités
   vx = ex, pour une seule instruction d'équations. 
   à la fin on peut simplement flatten cette liste.
   (cf article 18pages source à vérifier)
   De plus chaque vars telque x = (x0, x1 .. xn) 
   est appelé un "stream".

*)
let ast_to_astaez (tnode : Typed_ast.t_node) =
  let name =
    tnode.tn_name in

  let input = (* DONE *)
    List.map var_aez tnode.tn_input in

  let output = (* DONE *)
    List.map var_aez tnode.tn_output in

  let local = (* DONE *)
    List.map var_aez tnode.tn_local in
  
  Printf.printf "Liste des patterns:\n";
  List.iter (fun (eq: Typed_ast.t_equation) ->
      List.iter (fun (patt: Ident.t) -> Printf.printf "%s\n" patt.name) eq.teq_patt.tpatt_desc) tnode.tn_equs;

  Printf.printf "Liste des elements de Iota:\n";
  Iota.iter (fun k e -> Printf.printf "%s , %s\n" (k) (Hstring.view e)) symboles.env;
  
  let equs = (* PARTIALLY DONE *)
    List.flatten (List.map equs_aez tnode.tn_equs) in

  let loc = (* DONE *)
    tnode.tn_loc in
  { node_name = name;
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
    node_loc = loc;
  }



(* Ici on récupère l'enregistrement aezdifier
   et on effectue l'étape de model checking 
   avec Aez.
*)

  
let aezdify (ast_node: Typed_ast.t_node list) k =
  let laez = List.map ast_to_astaez ast_node in
  (*on recupere le premier node aez dans laliste laez*)
  let aez_node=List.hd laez in 
  let variables=  aez_node.node_output(*c la liste des outputs pour chaque aeznode*)

  let {name=variable} , _ =
    List.find(fun({name}, _) ->String.lowercase name = "ok") variables

   in 


let module BMC_solver =Smt.make(struct end) in
   begin
(*on recupere la liste des equations du node aez*)
  let l_formula =aez_node.node_equs in
  let delta i l_formula= Formula.make Formula.And l_formula
  for i=0 to k-1 do 
    let delta_i = delta i l_formula in (*c'est la ou on recupere la liste des equations avec n =0 , n=1 .......avec f-formula c'est une focntion qui prend comme parametre u n entier est retourne une formule de ttes les des des equations*)
    BMC_solver.assume ~id:0 delta_i

done;

  BMC_solver.check();

 for i=0 to k-1 do 
   let equation = ((Term.make_app variable i)===T.t_true) in 

   if not(BMC.entails ~id:0 equation) then raise BASE_CASE_FAILS
   done;

end;


(*deuxime cas c'est le cas inductive*)

let module IND_solver=Smt.make(struct end) in 
  begin
 let n = Term.make_app (declare_symbol "n" [] Type.type_int) []in 
 let l_formula =aez_node.node_aqus in
 let delta i l_formula= Formula.make Formula.And l_formula in 
    for i= 0 to k do 

(* ∆(n) , ∆(n+1) ...P(n),P(n+1)...P(n+k)|= P(n+k+1)*) 
 let kprim = Term.make_arith Term.Plus n (Term.make_int (Num.Int i) ) in
   
 let delta_i = delta kpim l_formula in (*c'est la ou on recupere la liste des equations avec n =0 , n=1 .......avec f-formula c'est une focntion qui prend comme parametre u n entier est retourne une formule de ttes les des des equations*)
    IND_solver.assume ~id:0 delta_i
if i < k
 then IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0);kprim] ;

if i >0
 then 
  begin
   let equation = ((Term.make_app variable i) === T.t_true) in 
    IND.assume ~id:0 equation 
 
  end;

done;

IND_solver.check();

let formula=(Term.make_app variable n)===T.t_true) in 

( if(not (IND_solver.entails ~id:0 (formula))
then raise FALSE_PROPERTY );

end;

TRUE_PROPERTY
with
  |BASE_CASE_FAILS ->Format.printf "property base false";
  |FALSE_PROPERTY   ->Format.printf "property false";





 



 Format.printf "End of aezdify \n"
  failwith "transform_aez::aezdify::Under Implementation"
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
