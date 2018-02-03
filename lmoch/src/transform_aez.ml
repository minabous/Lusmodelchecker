open Aez
open Smt
open Num
open Typed_aez

let i = ref 0
             
let declare_symbol (node:z_node) (name:String.t) t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  node.symboles <- Iota.add name x node.symboles;
  Printf.printf ", %s)\n" (Hstring.view x);
  x
   
let var_aez (node:z_node) (input : Ident.t * Asttypes.base_ty) =
  Printf.printf "var_aez\n";
  match input with
  | (v, ty) ->
     Printf.printf "Nom des variables+Hstring : (%s" v.name;
     match ty with
     | Asttypes.Tbool ->
        (declare_symbol node v.name [Type.type_int] Type.type_bool, ty)
     | Asttypes.Tint  ->
        (declare_symbol node v.name [Type.type_int] Type.type_int, ty)
     | Asttypes.Treal ->
        (declare_symbol node v.name [Type.type_int] Type.type_real, ty)
     | _ -> failwith "transform_aez::var_aez::Unknown type\n Type Has to be int, bool float"

  
(* 
   Ici pour chaque Patt = expr, on renvoit une Formula
   afin de construire la liste des formules à prouver
*)

let rec make_term expr =
  Printf.printf "Make_term\n";
  match expr with
  | Typed_ast.TE_const(c) ->
     begin
       match c with
       | Asttypes.Cbool(b) ->
          begin
            match b with
            | true  -> Term.t_true
            | false -> Term.t_false
          end
       | Asttypes.Cint(i) ->  Term.make_int (Int i)
       | Asttypes.Creal(f) -> Term.make_real (Num.num_of_string (string_of_float f))
       | _ -> failwith "transform_aez::make_term::Unknown constant type (only int are available yet)"
     end
  | _ ->
     failwith "transform_aez::make_term::Not Implemented"
          
    
let rec make_formula
          (node: z_node)
          (sym: Aez.Hstring.t)
          (expr: Typed_ast.t_expr_desc)
          (n: int) =
  let formula =
    Format.printf "%s" __LOC__;
    match expr with
  (* Amina: 
   Pourquoi expr et pas Const(c) directement ici.*)
  | Typed_ast.TE_const(c) ->
     Formula.make_lit Formula.Eq
       [ Term.make_app sym [Term.make_int (Num.Int n)] ; make_term expr ]
    
  | Typed_ast.TE_ident(id) ->
     let var = Iota.find id.name node.symboles in
     Formula.make_lit Formula.Eq
       [ Term.make_app sym [Term.make_int (Num.Int n)];
         Term.make_app var [Term.make_int (Num.Int n)] ]
     
  | Typed_ast.TE_op (op, el) ->
     begin
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
               Formula.make_lit Formula.Eq
                 [Term.make_app sym [Term.make_int (Num.Int n)];
                  Term.make_arith Term.Plus
                    (make_term e1.texpr_desc)
                    (make_term e2.texpr_desc)]
          end
       | _ ->
          failwith "transform_aez::make_formula::List match operators not implemented"
     end
  | _ -> failwith "transform_aez::make_formula::List match expressions not implemented"
  in
  Smt.Formula.print Format.std_formatter formula;
  formula
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
       | Op_lt  -> Formula.make
       | Op_le  ->
       | Op_gt  ->
       | Op_ge  ->
  
          | Op_not   ->
          | Op_and   ->
          | Op_or   ->
          | Op_impl ->
          | Op_if   ->
   *)

(* Eventuellement faire cette transformation 
 avant en créant un asttyped_aez pour ensuite parcourir une seul listes. *)
let create_couple_var_ty (node: z_node) (var:Ident.t) (ty: Asttypes.base_ty)
    : Aez.Hstring.t * Asttypes.base_ty =
  Printf.printf "Create_couple_var_ty\n";
    (Iota.find var.name node.symboles, ty)

  
let build_formula
      (node:z_node)
      (patty: Aez.Hstring.t * Asttypes.base_ty)
      (expr: Typed_ast.t_expr) =
  Printf.printf "Build_formula\n";
  let var_symbol = fst patty in
  (fun (n:int) -> make_formula node var_symbol expr.texpr_desc n)



(* Term = ite + operateur *)
(* Formula =  comparateur | combinateur *)
let normalize
      (node: z_node)
      (patts: (Hstring.t * Asttypes.base_ty) list)
      (exprs: Typed_ast.t_expr list) =
  Printf.printf "Normalize\n";
  let rec aux acc1 acc2
            (l1: (Hstring.t * Asttypes.base_ty) list)
            (l2: Typed_ast.t_expr list ) =
    match l1, l2 with
    | (a :: tla, b :: tlb) ->       
       begin
         match b.texpr_desc with
         | Typed_ast.TE_op(op, el) ->
            begin
              match op with
              | Op_eq | Op_neq
                | Op_lt | Op_le
                | Op_gt | Op_ge
                | Op_not| Op_and
                | Op_or ->
                 let fresh_var =
                   declare_symbol node (Printf.sprintf "aux%d" !i)
                     [Type.type_int]
                     Type.type_bool,
                   Asttypes.Tbool
                 in

                 (* S'il y a moyen de récupérer la valeur finale à
                    la fin du parsing alors initialiser i 
                    avec cette valeur + 1*)
                 let (id: Ident.t) = 
                   {id=(!i);
                    name=(Printf.sprintf "aux%d" !i);
                    kind=Ident.Prim;
                   }
                 in
                 let (fresh_expr:Typed_ast.t_expr) =
                   {                   
                     texpr_desc=Typed_ast.TE_ident(id);
                     texpr_type=[Asttypes.Tbool];
                     texpr_loc=b.texpr_loc;
                   }
                 in
                 incr i;
                 aux (acc1@
                        [a]
                        @
                          [fresh_var])
                   (acc2@[fresh_expr]@[b]) tla tlb
              | _ -> aux (acc1@[a]) (acc2@[b]) tla tlb
            end
         | _ -> aux (acc1@[a]) (acc2@[b]) tla tlb
       end
    | ([], []) -> (acc1, acc2)
    | _ ->
       failwith "transform_aez::normalize::Invalid_argument"
  in
  aux [] [] patts exprs

(* Cette fonction créée la liste des formules pour construire
 le raisonnement kind par la suite. *)
(* List.map2 (fun x y -> ()) [] [] *) (* Unit debug expression *)
let equs_aez (node:z_node) (equs: Typed_ast.t_equation) =
  Printf.printf "Equs_aez\n";
  let vars = equs.teq_patt.tpatt_desc in
  let tys = equs.teq_patt.tpatt_type in
  let patts = List.map2 (create_couple_var_ty node) vars tys in
  let exprs =
    match equs.teq_expr.texpr_desc with
    | Typed_ast.TE_tuple(el) -> el
    | _ -> [equs.teq_expr]
  in
  (* D'abord une étape de traitement*)
  let patterns, expressions =
    normalize
      node
      patts
      exprs
  in
  List.map2 (build_formula node)
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
  Printf.printf "Function:ast_to_aez\n";
  Printf.printf "Node:%s\n" tnode.tn_name.name;
  let node =
    { node_name = tnode.tn_name;
      node_input = [];
      node_output = [];
      node_vlocal = [];
      node_equs = [];
      node_loc = tnode.tn_loc;
      symboles = Iota.empty;
    }
  in   
  let input = (* DONE *)
    List.map (var_aez node) tnode.tn_input in
  let output = (* DONE *)
    List.map (var_aez node) tnode.tn_output in  
  let local = (* DONE *)
    List.map (var_aez node) tnode.tn_local in
  
  Printf.printf "Liste des patterns:\n";
  List.iter (fun (eq: Typed_ast.t_equation) ->
      List.iter (fun (patt: Ident.t) -> Printf.printf "%s\n" patt.name) eq.teq_patt.tpatt_desc) tnode.tn_equs;
  Printf.printf "Liste des elements de Iota:\n";
  Iota.iter (fun k e -> Printf.printf "%s , %s\n" (k) (Hstring.view e)) node.symboles;
  let equs = (* PARTIALLY DONE *)
    List.flatten (List.map (equs_aez node) tnode.tn_equs) in
  { node with
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
  }

  (* Ici on récupère l'enregistrement aezdifier
   et on effectue l'étape de model checking 
   avec Aez.
*)

(* Stephane: Ici BMC est comme une structure en C 
   alors tu peux le déclarer dehors *)
module BMC_solver = Smt.make(struct end)
(* Point d'entrée *)  
let aezdify (ast_node: Typed_ast.t_node list) k =
  Printf.printf "aezdify\n";
  let laez = List.map ast_to_astaez ast_node in
  Printf.printf "End of aezdify \n";
  (*on recupere le premier node aez dans laliste laez*)
  let aez_node = List.hd laez in 
  let variables = aez_node.node_output (*c la liste des outputs pour chaque aeznode*) in

  (* Stephane: Je ne sais pas ce que tu veux faire ici ?
   Quelques explications ? *)
  let {name=variable} , _ =
    List.find(fun({name}, _) -> String.lowercase name = "ok") variables
  in 


  (* Stephane: Je vois ce que tu veux faire ici 
     mais je ne pense pas que ça marchera de cette façon.
     essaye de réécrire la fonction exaclement comme sur la feuille
     ... que j'ai gardé.. désolé....
   *)  
  (*on recupere la liste des equations du node aez*)
  let l_formula = aez_node.node_equs in
  let delta i l_formula = Formula.make Formula.And l_formula
  for i=0 to k-1 do 
    let delta_i = delta i l_formula in (*c'est la ou on recupere la liste des equations avec n =0 , n=1 .......avec f-formula c'est une focntion qui prend comme parametre u n entier est retourne une formule de ttes les des des equations*)
    BMC_solver.assume ~id:0 delta_i

done;

  BMC_solver.check();

 for i=0 to k-1 do 
   let equation = ((Term.make_app variable i)===T.t_true) in 

   if not(BMC_solver.entails ~id:0 equation) then raise BASE_CASE_FAILS
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
   
   (*c'est la ou on recupere la liste des equations avec n =0 , n=1 .......avec f-formula c'est une focntion qui prend comme parametre u n entier est retourne une formule de ttes les des des equations*)
   let delta_i = delta kpim l_formula in
   IND_solver.assume ~id:0 delta_i
   if i < k
 then IND_solver.assume ~id:0 (Formula.make_lit Formula.Le [Term.make_int (Num.Int 0);kprim] ;

if i > 0
 then 
  begin
   let equation = ((Term.make_app variable i) === T.t_true) in 
   IND_solver.assume ~id:0 equation 
   
  end;
                               
  done;
                               
  IND_solver.check();
let formula = (Term.make_app variable n)===T.t_true) in 

( if(not (IND_solver.entails ~id:0 (formula))
then raise FALSE_PROPERTY );

end;

TRUE_PROPERTY
with
  |BASE_CASE_FAILS ->Format.printf "property base false";
  |FALSE_PROPERTY   ->Format.printf "property false";
                      
  failwith "transform_aez::aezdify::Under Implementation"
(* TODO *)
