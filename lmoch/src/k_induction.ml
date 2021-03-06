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
  let eqs = (List.map (fun f -> f n) formulas) in  
  Formula.make Formula.And eqs
  
  
(* ******************************************************************** *)
(** p_incr: Génère la formule de conjonction entre toutes les formules
    de la forme out = true  pour le noeud en question.
    @param: Un terme n spécifiant l'étape d'induction ( 0, 1, puis n, n+1)
            La liste des variables de sortie.
            Une Map dans laquelle est stocké l'ensemble des symboles
            de type Hstring.t.
    @return: Formula.t
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
     Formula.make_lit Formula.Eq [ Term.make_app sym [n] ; Term.t_true ]
  | _ ->
     Formula.make Formula.And
       (List.map
          (fun out_i ->
            let sym_i = (Iota.find (fst out_i) symboles) in
            Formula.make_lit Formula.Eq [ Term.make_app sym_i [n] ; Term.t_true ])
          outs) 


(* *************************************************************** *)
(* Cas de base *)
(** assumes: Fonction qui intégres les formules dans les assomptions
             du solver, puis qui vérifie ces assomptions.

    @param: Un constructeur de formules (delta_incr ou p_incr).
            Une liste de formules.
            Un k pour spécifier le k de l'induction.
    @return : unit
  *)
let assumes goal formul_list k =
  Printf.printf "Assuming: Base case conditions\n"; 
  for i = 0 to k - 1 do
    try
      BMC_solver.assume ~id:0 (goal (Term.make_int (Num.Int i)) formul_list)
    with
    | Smt.Unsat il -> Printf.printf "Raise->Base:(Assumes delta_incr 0 1): Unsat\n"
    (* | e -> Printf.printf "Raise->(Assumes delta_incr 0 1):?\n" (\* Le raise tombe ici donc il faut vérifier à quelle exception on a affaire *\) *)
  done;
  begin
    try
      BMC_solver.check()
    with
    | Smt.Error e ->
       begin
         Printf.printf"Raise->Base:Check\n";
         match e with
         | Smt.DuplicateTypeName(hs)
           | Smt.DuplicateSymb(hs) ->
            Printf.printf"Duplicate Symbol or Type %s\n" (Hstring.view hs)
         | Smt.UnknownType(hs)
           | Smt.UnknownSymb(hs) ->
            Printf.printf"Unknown Symbol or Type %s\n" (Hstring.view hs)
       end
    | Smt.Unsat il ->
       Printf.printf"Raise->Base:Check: Unsat\n"
    | _ ->
       Printf.printf"Raise->Base:Check: ?\n"
  end
  
let init n f =
  if n < 0 then raise (Invalid_argument "init");
  let rec ini i acc =
    if i = 0 then acc
    else ini (i-1) (f (i-1) :: acc)
  in
  ini n []            


(** entails: Fonction qui intégre au solver une conjonction des formules
             a prouver et effectue la vérification de ces formules
             en considérant les assomptions déja établies.
             
    @param: Un constructeur de formules (delta_incr ou p_incr).
            Une liste de formules.
            Un k pour spécifier le k de l'induction.
    @return : boolean
 *)
let entails outs symboles =
  Printf.printf"Entailing: Base case conditions\n";
  let base =
    try
      BMC_solver.entails ~id:0 (Formula.make Formula.And (init 2 (fun i -> p_incr (Term.make_int (Num.Int i)) outs symboles)))
    with
    | e -> Printf.printf "Raise->Base:Entails delta_incr 0 1\n"; false
  in
  base

(** chec: Fonction qui automatise la vérification d'un noeuds
          en suivant le processus de la k induction :
          Vérifier le cas de base, vérifier l'indiciton.

    @param: Un z_noeud ayant déja des formules prêtes.
            Un k pour spécifier le k de l'induction.
    @return : unit
  *)
let check (node: z_node ) (k: int) =
  (* On récupère les listes variables du noeuds*)
  let outs = node.node_output in
   let ins = node.node_input in
   let locs = node.node_vlocal in 
  
  (* On récupère la listes des lambda-fonctions générant les formules *)
  let formules = node.node_equs in
  try
    let base =
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
          | e -> Printf.printf "Raise->Ind:Assume: 0 <= n\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (delta_incr n formules)
          with
          | e -> Printf.printf "Raise->Ind:Assume: delta_incr n\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (delta_incr n_plus_one formules)
          with
          | e -> Printf.printf "Raise->Ind:Assume: delta_incr n+1\n"
        end;
        begin
          try
            IND_solver.assume ~id:0 (p_incr n outs node.symboles)
          with
          | e -> Printf.printf "Raise->Ind:Assume: p_incr n\n"
        end;
        (**************************optimisation ::path compression****************************)
        begin
          try
            let t_i =
              Term.make_app (Transform_aez.declare_symbol_ws node "i" [] Type.type_int) [] in
            let t_j =
              Term.make_app (Transform_aez.declare_symbol_ws node "j" [] Type.type_int) [] in
            
            let left = Formula.make Formula.And 
	                 [ 
	                   Formula.make_lit Formula.Lt [t_i ; t_j] ; 
	                   Formula.make_lit Formula.Le [t_j ; n]
                         ]
            in 
            let eqs =
              let fmatch =
                ( List.map
                    (fun (id, _) -> 
                      let var1 =
                        Transform_aez.declare_symbol_ws node id.Ident.name [] Type.type_int in
                      Formula.make_lit Formula.Neq
                        [
                          Term.make_app (var1) [t_i] ;
                          Term.make_app (var1) [t_j]  
                        ] 
                    ) 
                    (locs @ ins ) ) in
              match fmatch with
              | []  -> Formula.f_false
              | [eq] -> Formula.make Formula.Imp [left ; eq]
              | eqs -> Formula.make Formula.Imp [left ; Formula.make Formula.Or eqs ]
            in          
            IND_solver.assume ~id:0 eqs ;
          with
          | Smt.Error e ->
             begin
               Printf.printf"Raise->IND_opti:Assumes: ";
               match e with
               | Smt.DuplicateTypeName(hs)
                 | Smt.DuplicateSymb(hs) ->
                  Printf.printf"Duplicate Symbol or Type %s\n" (Hstring.view hs)
               | Smt.UnknownType(hs)
                 | Smt.UnknownSymb(hs) ->
                  Printf.printf"Unknown Symbol or Type %s\n" (Hstring.view hs)
             end
          | Smt.Unsat il ->
             Printf.printf"Raise->IND_opti:Assumes: Unsat\n"
          | _ ->
             Printf.printf"Raise->IND_opti:Assumes: ?\n"
            
        end;   
        (******************************************************************)

        
        begin
          try
            IND_solver.check()
          with
          | e -> Printf.printf "Raise->Ind:Check: ?\n"
        end;
        Printf.printf"Entailing: k-ind case conditions\n";
        try
          IND_solver.entails ~id:0 (p_incr n_plus_one outs node.symboles)
        with
        | e -> Printf.printf "Raise->Ind:Entails p_incr n+1\n"; false
      in
      if ind then (raise TRUE_PROPERTY)
      else (raise UNKNOWN_PROPERTY)
  with
  | TRUE_PROPERTY -> Printf.printf "TRUE PROPERTY\n"	
  | FALSE_PROPERTY -> Printf.printf "FALSE PROPERTY\n"
  | UNKNOWN_PROPERTY -> Printf.printf "UNKNOWN PROPERTY\n"

