open Aez
open Smt
open Num
module F = Formula
module T = Term
open Typed_aez
   
exception FALSE_PROPERTY
exception TRUE_PROPERTY
exception BASE_CASE_FAILS

module BMC_solver = Smt.Make(struct end) 
module IND_solver = Smt.Make(struct end)


(* *************************************************************** *)
(** delta_incr: Génère la conjonction de toutes les formules 
    représentant la définition logique du noeud.
    @params:
    @return:

 **)
let delta_incr (i:int) formulas =
  Formula.make Formula.And (List.map (fun f -> f i) formulas)



  
(* *************************************************************** *)
(** p_incr: Génère la formule de conjonction entre toutes les formules
    de la forme out = true  pour le noeud en question.
    @param:
    @return:
 **)
let p_incr (i:int) oks =
  Formula.make Formula.And
    (List.map
       (fun out_i -> Formula.make_lit Formula.Eq [Term.make_app out_i [i] ; Term.t_true])
       oks) 




(* *************************************************************** *)
(*cas de base*)
let bmc k =
  Format.printf "Bmc : node base case " ; 
  for i = 0 to k - 1 do 
    let delta_i = delta i formul_list in
    BMC_solver.assume ~id:0 (delta_i);
  done;
  BMC_solver.check();

  Format.printf"checking base case condition\n";
  for i = 0 to k-1 do 
    let ok_i = p_incr_i i variable  in 
    if not (BMC_solver.entails ~id:0 ok_i) then (raise BASE_CASE_FAILS) 
  done;
  

  let check node_list (k: int) =
  (*on recupere le premier node aez dans la liste list_aez*)
  let aez_node = List.hd node_list in
  (* On récupère les variables de sorties *)
  let variables_out_list = aez_node.node_output in
      
  (* On va chercher la 1er variable out de la liste *)
  (* De manière générale automatiser pour "m" output *)
  let out = List.hd variables_out_list in  
  
  (* On récupère la listes des lambda-fonctions *)
  let formul_list = aez_node.equs in
  
  (* Stephane: Meme chose ici.*)
  (* let ok_i = p_incr_i i out  in *) 
  (* let base =  if not (BMC_solver.entails ~id:0 p_incr_i) then (raise BASE_CASE_FAILS) *)
  let base =
    bmc k;
    entails 
    BMC_solver.entails ~id:0 Formula.make Formula.And List.init k (fun i -> p_incr i out) in

  let n =
    Term.make_app (declare_symbol "n" [] Type.type_int) [] in 
  
  let kind k =
    for i = 0 to k do 
      let kprim = Term.make_arith Term.Plus n (Term.make_int(Num.Int i)) in
      let delta_i = delta kprim formul_list in
      let ok_i = p_incr_i kprim variable  in
      (* ∆(n) , ∆(n+1) ...P(n),P(n+1)...P(n+k)|= P(n+k+1)*) 
      IND_solver.assume ~id:0 (delta_i);
      IND_solver.check ();
      IND_solver.assume  ~id:0 ok_i;
      if (IND_solver.entails ~id:0 ok_i)
      then (raise FALSE_PROPERTY);
      
      if (i < k)
      then IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int   (Num.Int 0);kprim] );
      
    done;
    raise TRUE_PROPERTY

  with
   | TRUE_PROPERTY -> Format.printf "TRUE PROPERTY"	
   | FALSE_PROPERTY  -> Format.printf "FALSE PROPERTY"
   | BASE_CASE_FAILS ->Format.printf "Base case fails"























(* open Aez
 * open Smt
 * (\* open Transform_aez *\)
 * 
 * exception BASE_CASE_FALSE
 * exception TRUE_PROPERTY
 * exception FALSE_PROPERTY
 * 
 * 
 * 
 * 
 * module BMC_solver = Smt.Make(struct end)
 * module IND_solver = Smt.Make(struct end)
 * 
 *   
 * let induction kprim nodes ({tn_input; tn_output; tn_local; tn_equs} as node)=
 *    try 
 * (\*cas de base ∆(0) , ∆(1) ......|= P(0)∧P(1).......P(K)  *\)
 *     Format.printf"Prooving the base case\n"
 * 
 *      for i=0 to kprim-1 do
 *       BMC_solver.assume ~id:0 (delta_incr i);
 *      done;
 *       BMC_solver.check();
 *        
 *     for i=0 to kprim-1 do 
 *       if not(BMC_solver.entails ~id:0 (ok i)) then raise (Base_Case_Fails );
 *      done;
 * 
 * (\*cas de base ∆(n) , ∆(n+1) ...P(n),P(n+1)...P(n+k)|= P(n+k+1)  *\)
 * 
 * let induct k =
 *   let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
 *     Format.printf"Prooving the inductive case\n"
 *       for(i =0 to kprim ) do 
 *         IND_solver.assume ~id:0 (delta_incr i);
 *         if(i < kprim) then 
 *           Kind_solver.assume ~id:0 (Formula.make_lit Formula.Lt [Term.make_int (Num.Int kprim); n]);
 *         
 *         if(i>0)
 *         then begin
 *             
 *      end
 * 
 *                IND_solver.check() ;
 * 
 *         if not (Inductive_solver.entails ~id:0 (ok )) then raise (False_Property)
 * 
 * 
 * end;
 * 
 *    TRUE_PROPERTY
 * 
 *   with
 *     |False_Property  ->  Format.printf "FALSE PROPERTY";
 *    
 *     |Base_Case_Fails ->   Format.printf "FALSE PROPERTY"; *)


















