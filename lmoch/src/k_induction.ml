open Aez
open Smt
open Num
module F = Formula
module T = Term
open Typed_aez
   
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
let delta_incr (n: Term.t) (formulas: (Smt.Term.t -> Aez.Smt.Formula.t) list) =
  Formula.make Formula.And (List.map (fun f -> f n) formulas)
  
  
(* *************************************************************** *)
(** p_incr: Génère la formule de conjonction entre toutes les formules
    de la forme out = true  pour le noeud en question.
    @param:
    @return:
 **)
let p_incr (n: Term.t) (outs: z_var list) (symboles: Hstring.t Iota.t) =
  (* Donc ici on fait la séparation pour ne pas se retrouver
     avec Make And [ok(n)] 
   *)
  match outs with    
  | [] ->
     raise (Invalid_argument "p_incr")
  | [out] ->
     let sym = (Iota.find (fst out) symboles) in
     Formula.make_lit Formula.Eq [Term.make_app sym [n] ; Term.t_true]
  | _ ->
     Formula.make Formula.And
       (List.map
          (fun out_i ->
            let sym_i = (Iota.find (fst out_i) symboles) in
            Formula.make_lit Formula.Eq [Term.make_app sym_i [n] ; Term.t_true])
          outs) 


(* *************************************************************** *)
(* Cas de base *)
let assumes goal formul_list k =
  Printf.printf "Assuming: Base case conditions\n"; 
  for i = 0 to k - 1 do
    try
      BMC_solver.assume ~id:0 (goal (Term.make_int (Num.Int i)) formul_list)
    with
    | Smt.Unsat il -> Printf.printf "Raise->(Assumes delta_incr 0 1):Unsat\n"
    (* | e -> Printf.printf "Raise->(Assumes delta_incr 0 1):?\n" (\* Le raise tombe ici donc il faut vérifier à quelle exception on a affaire *\) *)
  done;
  begin
    try
      BMC_solver.check()
    with
    | Smt.Error e ->
       begin
         Printf.printf"Raise->Check:Base\n";
         match e with
         | Smt.DuplicateTypeName(hs)
           | Smt.DuplicateSymb(hs) ->
            Printf.printf"Duplicate Symbol or Type %s\n" (Hstring.view hs)
         | Smt.UnknownType(hs)
           | Smt.UnknownSymb(hs) ->
            Printf.printf"Unknown Symbol or Type %s\n" (Hstring.view hs)
       end
    | Smt.Unsat il ->
       Printf.printf"Raise->Check:Base:Unsat\n"
    | _ ->
       Printf.printf"Raise->Check:Base:?\n"
  end
  
let init n f =
  if n < 0 then raise (Invalid_argument "init");
  let rec ini i acc =
    if i = 0 then acc
    else ini (i-1) (f (i-1) :: acc)
  in
  ini n []            

let entails outs symboles =
  Printf.printf"Entailing: Base case conditions\n";
  let base =
    try
      BMC_solver.entails ~id:0 (Formula.make Formula.And (init 2 (fun i -> p_incr (Term.make_int (Num.Int i)) outs symboles)))
    with
    | e -> Printf.printf "Raise->Assumes delta_incr 0 1\n"; true
  in
  base
           
let check (node: z_node ) (k: int) =
  (* On récupère le premier node aezdifier dans la liste des noeuds *)
  (* De manière générale: Récupèrer le nom du node checker *)
  (* A l'entrée du programme. *)
  (* Si aucun nom spécifié, tentez de checker tout les nodes comme *)
  (* avec frama-c.  *)


  (* On récupère les variables de sorties *)
  let outs = node.node_output in
  
  (* On récupère la listes des lambda-fonctions générant les formules *)
  let formules = node.node_equs in
  try
    let base =
      (*Printf.printf "Bounded Model Checking\n";*)
      assumes delta_incr formules k;
      entails outs node.symboles
    in
    if not base then (raise FALSE_PROPERTY)
    else
      let n =
        Term.make_app (Transform_aez.declare_symbol_ws node "n" [] Type.type_int) [] in 
      let n_plus_one =
        Term.make_arith Term.Plus n (Term.make_int (Num.Int 1)) in
      let ind =
        Printf.printf "Assuming: k-ind case conditions\n"; 
        begin
          try
            IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0); n])
          with
          | e -> Printf.printf "Raise->Assume 0 <= n\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (delta_incr n formules)
          with
          | e -> Printf.printf "Raise->Assume delta_incr n\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (delta_incr n_plus_one formules)
          with
          | e -> Printf.printf "Raise->Assume delta_incr n+1\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (p_incr n outs node.symboles)
          with
          | e -> Printf.printf "Raise->Assume p_incr n\n"
        end;
        begin
          try
            IND_solver.check()
          with
          | e -> Printf.printf "Raise->Check:Ind\n"
        end;
        Printf.printf"Entailing: k-ind case conditions\n";
        IND_solver.entails ~id:0 (p_incr n_plus_one outs node.symboles)
      in
      if ind then (raise TRUE_PROPERTY)
      else (raise UNKNOWN_PROPERTY)
  with
  | TRUE_PROPERTY -> Printf.printf "TRUE PROPERTY\n"	
  | FALSE_PROPERTY  -> Printf.printf "FALSE PROPERTY\n"
  | UNKNOWN_PROPERTY -> Printf.printf "UNKNOWN PROPERTY\n"
















