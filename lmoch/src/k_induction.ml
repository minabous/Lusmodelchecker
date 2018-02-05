open Aez
open Smt
open Num
module F = Formula
module T = Term
   
exception FALSE_PROPERTY
exception TRUE_PROPERTY
exception UNKNOWN_PROPERTY

module BMC_solver = Smt.Make(struct end) 
module IND_solver = Smt.Make(struct end)

(* *************************************************************** *)
(** delta_incr: Génère la conjonction de toutes les formules 
    représentant la définition logique du noeud.
    @params:
    @return:

 **)
let delta_incr (n: Term.t) formulas =
  Formula.make Formula.And (List.map (fun f -> f n) formulas)

  
(* *************************************************************** *)
(** p_incr: Génère la formule de conjonction entre toutes les formules
    de la forme out = true  pour le noeud en question.
    @param:
    @return:
 **)
let p_incr (n: Term.t) outs =
  Formula.make Formula.And
    (List.map
       (fun out_i -> Formula.make_lit Formula.Eq [Term.make_app (fst out_i) [n] ; Term.t_true])
       outs) 


(* *************************************************************** *)
(* Cas de base*)
let assumes goal formul_list k =
  Printf.printf "Assuming: Base case conditions\n" ; 
  for i = 0 to k - 1 do 
    BMC_solver.assume ~id:0 (goal (Term.make_int (Num.Int i)) formul_list);
  done;
  BMC_solver.check()


let entails outs =
  Printf.printf"Entailing: Base case conditions\n";
  BMC_solver.entails ~id:0 (Formula.make Formula.And (List.init 2 (fun i -> p_incr (Term.make_int (Num.Int i)) outs)))  

let check (node_list: Typed_aez.z_node list) (k: int) =
  (* On récupère le premier node aezdifier dans la liste des noeuds *)
  (* De manière générale: Récupèrer le nom du node checker *)
  (* A l'entrée du programme. *)
  (* Si aucun nom spécifié, tentez de checker tout les nodes comme *)
  (* avec frama-c.  *)
  let node = List.hd node_list in

  (* On récupère les variables de sorties *)
  let outs = node.node_output in
  
  (* On récupère la listes des lambda-fonctions générant les formules *)
  let formules = node.node_equs in
  try
    let base =
      Printf.printf "Bounded Model Checking\n";
      assumes delta_incr formules k;
      entails outs
    in
    if not base then (raise FALSE_PROPERTY)
    else
      let n =
        Term.make_app (Transform_aez.declare_symbol node "n" [] Type.type_int) [] in 
      let n_plus_one =
        Term.make_arith Term.Plus n (Term.make_int (Num.Int 1)) in
      let ind =
        IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n]);
        IND_solver.assume ~id:0 (delta_incr n formules);
        IND_solver.assume ~id:0 (delta_incr n_plus_one formules);
        IND_solver.assume ~id:0 (p_incr n outs);
        IND_solver.check();
        IND_solver.entails ~id:0 (p_incr n_plus_one outs)
      in
      if ind then (raise TRUE_PROPERTY)
      else (raise UNKNOWN_PROPERTY)

        (* for i = 0 to k do 
         *   let kprim = Term.make_arith Term.Plus n (Term.make_int(Num.Int i)) in
         *   let delta_i = delta kprim formul_list in
         *   let ok_i = p_incr_i kprim variable  in
         *   (\* ∆(n) , ∆(n+1) ...P(n),P(n+1)...P(n+k)|= P(n+k+1)*\) 
         *   IND_solver.assume ~id:0 (delta_i);
         *   IND_solver.check ();
         *   IND_solver.assume  ~id:0 ok_i;
         *   if (IND_solver.entails ~id:0 ok_i)
         *   then (raise FALSE_PROPERTY);
         *   
         *   if (i < k)
         *   then IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int   (Num.Int 0);kprim] );
         *   
         * done;
         * raise TRUE_PROPERTY *)

      with
      | TRUE_PROPERTY -> Printf.printf "TRUE PROPERTY"	
      | FALSE_PROPERTY  -> Printf.printf "FALSE PROPERTY"
      | UNKNOWN_PROPERTY -> Printf.printf "UNKNOWN PROPERTY"











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


















