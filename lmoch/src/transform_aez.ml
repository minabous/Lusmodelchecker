open Aez
open Smt
open Num
open Typed_aez
open Asttypes
   
module TE = Typed_ast

let i = ref 0
let id_sym = ref 1
let debug = true

(** Fonction de debugging. Si b = true
    alors la fonction f affiche son résultat.
    
    @params: b:boolean
             f:unit -> unit
    @return: unit   
 **)
let debugging b f =
  if b then f() else ()
  
(* ********************* UTILS *********************** *)
(** Fonction qui déclare un symbole Hstring
    à partir d'un Ident.t 

 **)
let declare_symbol (node: z_node) (v: Ident.t) t_in t_out =
  let id_s = (Printf.sprintf "_%d" !id_sym) in
  let x = Hstring.make (v.name^id_s) in
  Symbol.declare x t_in t_out;
  node.symboles <- Iota.add v x node.symboles;
  debugging debug (fun () -> (Printf.printf "(%s, %s)\n" v.name (Hstring.view x)))


(** Fonction qui déclare un symbole Hstring
    à partir d'une chaine s
    (ws => "with string")

 **)
let declare_symbol_ws (node: z_node) (s: String.t) t_in t_out =
  let id_s = (Printf.sprintf "_%d" !id_sym) in
  let x = Hstring.make (s^id_s) in
  Symbol.declare x t_in t_out;
  debugging debug (fun () -> (Printf.printf "(%s, %s)\n" s (Hstring.view x)));
  x
(******************************************************************************)
(** Var_aez:Fonction qui crée un couple Hstring.t, type
    permettant de garder l'information du type de la variable.
    
    @params:            
    @return:
 **)
let var_aez (node: z_node) (input : TE.typed_var)
    : TE.typed_var  =
  debugging debug (fun () -> (Printf.printf "    <Var_aez>\n"));
  match input with
  | (v, ty) ->
     debugging debug (fun () -> (Printf.printf "    Nom des variables+Hstring:  "));
     match ty with
     | Asttypes.Tbool ->
        declare_symbol node v [Type.type_int] Type.type_bool;
        (v, ty)
     | Asttypes.Tint  ->
        declare_symbol node v [Type.type_int] Type.type_int;
        (v, ty)
     | Asttypes.Treal ->
        declare_symbol node v [Type.type_int] Type.type_real;
        (v, ty)
        
(* 
   Ici pour chaque Patt = expr, on renvoit une Formula
   afin de construire la liste des formules à prouver
 *)

(** Matching Operator:
    Fonction qui permet de sélectionner le bon
    opérateur pour la construction des termes.

    @params:            
    @return:
 **)
let arith op = 
  match op with 
  | Op_add | Op_add_f -> Term.Plus
  | Op_sub | Op_sub_f -> Term.Minus
  | Op_mul | Op_mul_f -> Term.Mult
  | Op_div | Op_div_f -> Term.Div
  | Op_mod -> Term.Modulo
  |_    -> failwith "incorrect operator"
let logic op =
  match op with 
  | Op_and -> Formula.And
  | Op_or -> Formula.Or
  | Op_impl -> Formula.Imp
  | Op_not -> Formula.Not
  | _ -> failwith "incorrect combinator"
let compare op =
  match op with
  | Op_eq -> Formula.Eq 
  | Op_lt -> Formula.Lt
  | Op_le -> Formula.Le
  | Op_neq -> Formula.Neq
  | _ -> failwith "incorrect comparator"
       

(* *********************** AEZ FORMULA ************************** *)
(** Formula_of: Fonction qui construit les formules 
    rencontrées dans les équations.
    @params:
    @return:
 **)
let rec formula_of
          node
          (expr: z_expr_desc)
          n =
  debugging debug (fun () -> (Printf.printf "Formula_of\n"));
  match expr with
  | Z_ident(id) ->
     Formula.make_lit Formula.Eq
       [ term_of node expr n ; Term.t_true ]
    
  | Z_const(c) ->
     begin
       match c with
       | Asttypes.Cbool(b) ->
          begin
            match b with
            | true  -> Formula.f_true
            | false -> Formula.f_false
          end
       | _ ->
          failwith "transform_aez::formula_of::Const expression has to be bool"
     end
  | Z_op(op, el) ->
     begin
       match op with
       | Comparator(o) ->
          let [e1; e2] = el in
          let e1', e2' = e1.zexpr_desc, e2.zexpr_desc in
          Formula.make_lit (compare o)
            [ term_of node e1' n;
              term_of node e2' n ]
          
       | Combinator(o) ->
          begin
            match o with
            | Op_not ->
               let [e] = el in
               let e' = e.zexpr_desc in
               Formula.make (logic o)
                 [ formula_of node e' n ]

            (* Ajout de l'opérateur xor ------ *)
            | Op_xor ->
               let [e1; e2] = el in
               let e1', e2' = e1.zexpr_desc, e2.zexpr_desc in
               Formula.make Formula.Or
                 [ Formula.make Formula.And
                     [formula_of node e1' n;
                      Formula.make Formula.Not [formula_of node e2' n] ] ;
                   
                   Formula.make Formula.And
                     [Formula.make Formula.Not [formula_of node e1' n];
                      formula_of node e2' n ] ;
                 ]
               
            | _ ->
               let [e1; e2] = el in
               let e1', e2' = e1.zexpr_desc, e2.zexpr_desc in
               Formula.make (logic o)
                 [ formula_of node e1' n;
                   formula_of node e2' n ]
               
          end
       | _ ->
          failwith "transform_aez::formula_of::Operator expression has to be bool"
     end
    
  | _ ->
     failwith "transform_aez::formula_of::Not Implemeted"
    
(* *************************** AEZ Term ************************** *)
(** Term_of:Fonction qui construit les termes
    rencontrés dans les équations.
    
    @params:            
    @return:
 **)
and term_of node (expr: z_expr_desc) n =
  debugging debug (fun () -> (Printf.printf "Term_of\n"));
  match expr with
  | Z_const(c) ->
     begin
       match c with
       | Asttypes.Cbool(b) ->
          begin
            match b with
            | true  -> Term.t_true
            | false -> Term.t_false
          end
       | Asttypes.Cint(i) ->  Term.make_int  (Num.Int i)
       | Asttypes.Creal(f) -> Term.make_real (Num.num_of_string (string_of_float f))
     end    
    
  | Z_ident(id) ->
     let var =
       Iota.find id node.symboles in
     Term.make_app var [n]
     
  | Z_op(op, el) ->
     begin
       match op with
       | Calculator(calc) ->
          begin
            match el with
            | [e1; e2] ->
               let e1, e2 =
                 e1.zexpr_desc, e2.zexpr_desc in 
               Term.make_arith
                 (arith calc)
                 (term_of node e1 n)
                 (term_of node e2 n)
            | _ ->
               debugging debug (fun () -> (Printf.printf "Z_op nbr d'opérandes : %d\n" (List.length el)));
               failwith "transform_aez::term_of::Two operandes expected"        
          end
       | Branchment(ite) ->
          begin
            match el with
            | [f; e1; e2] ->
               let f, e1, e2 =
                 f.zexpr_desc,
                 e1.zexpr_desc,
                 e2.zexpr_desc
               in
               Term.make_ite
                 (formula_of node f n)
                 (term_of node e1 n)
                 (term_of node e2 n)
            | _ ->
               debugging debug (fun () -> (Printf.printf "Op_if nbr de branches : %d\n" (List.length el)));
               failwith "transform_aez::term_of::Three expressions expected"
          end
       | Combinator(o) | Comparator(o) ->
          failwith (Printf.sprintf "transform_aez::term_of::[Operator=%s] : Expected an operator of type Calculator or Branchment" (Zprint.match_op o))  
     end
    
  | Z_arrow (e1 ,e2) ->
     let e1, e2 = e1.zexpr_desc, e2.zexpr_desc in
     Term.make_ite
       (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
       (term_of node e1 n)
       (term_of node e2 n)     
     
  | Z_pre(e) ->
     let e = e.zexpr_desc in
     term_of node e (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)))    
     
  | _ ->
     failwith "transform_aez::term_of::Not implemented"

let num = ref 1

(** Make_Formula:Fonction qui crée les formules
    représentant "pattern = expr ", c'est à dire
    l'ensemble des formules décrivant le comportement
    d'un noeud.
    @params:            
    @return:
 **)
let make_formula
      (node: z_node)
      (sym: Ident.t)
      (expr: z_expr_desc)
      (n: Term.t) =
  debugging debug (fun () -> (Printf.printf "<Make_formula>\n"));
  debugging debug (fun () -> (Printf.printf "sym=%s\n" sym.name));
  let formula =
    match expr with
    | Z_const(c) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_const(_)\n" (Hstring.view hsym)));
       
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_ident(id) ->
       let hsym = Iota.find sym node.symboles in
       let hvar = Iota.find id node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_ident(%s)\n" (Hstring.view hsym) (Hstring.view hvar)));
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           Term.make_app hvar [n] ]
       
    | Z_op ((Comparator(op)
             | Combinator(op)), el) ->
       let zexpr_list =
         [ { zexpr_desc=Z_ident(sym);
             zexpr_type=[Tbool];};
           { zexpr_desc=Z_const(Cbool(true));
             zexpr_type=[Tbool];} ]
       in
       let expr_aux = Z_op(Comparator(Op_eq), zexpr_list) in
       let aux_n = formula_of node expr_aux n in
       debugging debug (fun () -> (Zprint.print_expr_Zop op sym));
       
       Formula.make Formula.And
         [ Formula.make Formula.Imp [ aux_n; formula_of node expr n ] ;
           Formula.make Formula.Imp [ formula_of node expr n; aux_n ] ]
       
    | Z_op ((Calculator(op)
             | Branchment(op)), el) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Zprint.print_expr_Zop op sym));
       
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           term_of node expr n]
       
    | Z_arrow(_, _) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_arrow(_, _)\n" sym.name));
       (* Ici rien ne change ex000 *)
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           term_of node expr n ]
       
    | Z_pre(_) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_pre(_)\n" (Hstring.view hsym)));
       
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_prim(id, el) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_prim(%s, _)\n" (Hstring.view hsym) id.name));

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_tuple(_) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_tuple(_)\n" (Hstring.view hsym)));
       
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_app(id, _) ->
       let hsym = Iota.find sym node.symboles in
       debugging debug (fun () -> (Printf.printf "%s = TE_app(%s, _)\n" (Hstring.view hsym) id.name));
       
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | _ -> failwith "transform_aez::make_formula::List match expressions not implemented"
  in
  debugging debug (fun () ->  Printf.printf "(%d)  " !num;
                              incr num;
                              (Smt.Formula.print Format.std_formatter formula));
  print_newline();
  print_newline();
  formula
  
  
(** Create_couple_var_ty:Fonction qui 
    "pack" les varaibles avec leur types
    pour une utilisation future.
    
    @params:            
    @return:
 **)
let create_couple_var_ty
      (node: z_node)
      (var:Ident.t)
      (ty: Asttypes.base_ty)
  =
  debugging debug (fun () -> (Printf.printf "    <Create_couple_var_ty>\n"));
  (var, ty)
  

(** description:
    
    @params:            
    @return:
 **)
let build_formula
      (node: z_node)
      (patt_ty: Ident.t * Asttypes.base_ty)
      (expr: z_expr) =
  debugging debug (fun () -> (Printf.printf "    <Build_formula>\n"));
  let var_symbol = fst patt_ty in
  (fun (n: Term.t) -> make_formula node var_symbol expr.zexpr_desc n)


  
(** description:
    
    @params:            
    @return:
 **)
let generate_fresh_var node =
  let (id: Ident.t) = 
    {
      id=(!i);
      name=(Printf.sprintf "aux%d" !i);
      kind=Ident.Stream;
    }
  in
  declare_symbol node id
    [Type.type_int]
    Type.type_bool;
  let fresh_var = id, Asttypes.Tbool in

  let (fresh_expr:z_expr) =
    {                   
      zexpr_desc=Z_ident(id);
      zexpr_type=[Asttypes.Tbool];
    }    
  in
  incr i;
  (id, fresh_var, fresh_expr)



  
(** :
    
    @params:            
    @return:
 **)
let normalize
      (node: z_node)
      (patts: (Ident.t * Asttypes.base_ty) list)
      (exprs: z_expr list) =
  debugging debug (fun () -> (Printf.printf "    <Normalize>\n"));
  let rec fun_aux acc1 acc2
            (l1: (Ident.t * Asttypes.base_ty) list)
            (l2: z_expr list ) =
    match l1, l2 with
    | (a :: tla, b :: tlb) ->       
       begin
         match b.zexpr_desc with
         | Z_op((Comparator(op)|Combinator(op)), el) ->
            begin
              match op with
              | Op_eq | Op_neq
                | Op_lt | Op_le
                | Op_not| Op_and
                | Op_or | Op_impl ->
                 debugging debug (fun () -> Printf.printf "    Done!\n");
                 let id,fresh_var,fresh_expr = generate_fresh_var node in
                 (* S'il y a moyen de récupérer la valeur finale à
                    la fin du parsing alors initialiser i 
                    avec cette valeur + 1 *)
                 fun_aux (acc1@[a]@[fresh_var])
                   (acc2@[fresh_expr]@[b])
                   tla tlb
                 
              | _ -> fun_aux (acc1@[a]) (acc2@[b]) tla tlb
            end
           
         | Z_op(Branchment(o), el) ->
            begin
              debugging debug (fun () -> Printf.printf "    Done!\n");
              match b.zexpr_type with
              | [Tbool] ->
                 begin
                   let [f;e1;e2] = el in
                   match e1.zexpr_desc, e2.zexpr_desc with
                   | Z_const(_), Z_op(op, _) ->
                      let id,fresh_var,fresh_expr =
                        generate_fresh_var node in
                      let new_if =
                        {zexpr_desc=Z_op(Branchment(Op_if), [f;e1;fresh_expr]);
                         zexpr_type=b.zexpr_type;} in
                      fun_aux (acc1@[a]@[fresh_var])
                        (acc2@[new_if]@[e1])
                        tla tlb
                   | Z_op(op, _),  Z_const(_) ->
                      let id,fresh_var,fresh_expr =
                        generate_fresh_var node in
                      let new_if =
                        {zexpr_desc=Z_op(Branchment(Op_if), [f;fresh_expr;e2]);
                         zexpr_type=b.zexpr_type;} in
                      fun_aux (acc1@[a]@[fresh_var])
                        (acc2@[new_if]@[e1])
                        tla tlb
                      
                   | Z_op(_), Z_op(_) ->
                      let id1,fresh_var1,fresh_expr1 =
                        generate_fresh_var node in
                      let id2,fresh_var2,fresh_expr2 =
                        generate_fresh_var node in
                      let new_if =
                        {zexpr_desc=Z_op(Branchment(Op_if), [f;fresh_expr1;fresh_expr2]);
                         zexpr_type=b.zexpr_type;} in
                      fun_aux (acc1@[a]@[fresh_var1]@[fresh_var2])
                        (acc2@[new_if]@[e1]@[e2])
                        tla tlb
                 end                
              | _ -> fun_aux (acc1@[a]) (acc2@[b]) tla tlb
                   
            end
           
         | Z_arrow(e1, e2) ->
            begin
              let e1' ,e2' =
                e1.zexpr_desc,e2.zexpr_desc in
              match e1', e2' with
              | Z_op(Comparator(_), _),
                Z_op(Comparator(_), _)
                | Z_op(Combinator(_), _),
                  Z_op(Combinator(_), _)
                | Z_op(Comparator(_), _),
                  Z_op(Combinator(_), _)
                | Z_op(Combinator(_), _),
                  Z_op(Comparator(_), _) ->
                 debugging debug (fun () -> Printf.printf "    Done!\n");
                 let id1,fresh_var1,fresh_expr1 =
                   generate_fresh_var node in
                 let id2,fresh_var2,fresh_expr2 =
                   generate_fresh_var node in
                 let new_arrow =
                   {zexpr_desc=Z_arrow(fresh_expr1, fresh_expr2);
                    zexpr_type=b.zexpr_type;} in
                 fun_aux (acc1@[a]@[fresh_var1]@[fresh_var2])
                   (acc2@[new_arrow]@[e1]@[e2])
                   tla tlb

              | Z_const(_),
                Z_op((Comparator(_)|Combinator(_)), _) ->
                 debugging debug (fun () -> Printf.printf "    Done!\n");
                 let id,fresh_var,fresh_expr =
                   generate_fresh_var node in
                 let new_arrow =
                   {zexpr_desc=Z_arrow(e1, fresh_expr);
                    zexpr_type=b.zexpr_type;} in
                 fun_aux (acc1@[a]@[fresh_var])
                   (acc2@[new_arrow]@[e2]) (* <-- ex000 Ici j'avais mis b(=Z_arrow) a la place de e2 *)
                   tla tlb

              | Z_op((Comparator(_)|Combinator(_)), _),
                Z_const(_) ->
                 debugging debug (fun () -> Printf.printf "    Done!\n");
                 let id,fresh_var,fresh_expr =
                   generate_fresh_var node in
                 let new_arrow =
                   {zexpr_desc=Z_arrow(fresh_expr, e2);
                    zexpr_type=b.zexpr_type;} in
                 fun_aux (acc1@[a]@[fresh_var])
                   (acc2@[new_arrow]@[e1]) (* <-- ex000 Ici j'avais mis b(=Z_arrow) a la place de e1 *)
                   tla tlb
                 
              | _, _ -> fun_aux (acc1@[a]) (acc2@[b]) tla tlb
            end
         | _ -> fun_aux (acc1@[a]) (acc2@[b]) tla tlb
       end
    | ([], []) -> (acc1, acc2)
    | _ ->
       failwith "transform_aez::normalize::Invalid_argument"
  in
  fun_aux [] [] patts exprs


(* Cette fonction créée la liste des formules pour construire
 le raisonnement kind par la suite. *)
(** Equs_aez:
    
    @params:            
    @return:
 **)
let equs_aez (node:z_node) (equs: z_equation) =
  debugging debug (fun () -> (Printf.printf "\n<Equs_aez>\n"));
  let vars = equs.zeq_patt.tpatt_desc in
  let tys = equs.zeq_patt.tpatt_type in
  let patts = List.map2 (create_couple_var_ty node) vars tys in
  let exprs =
    match equs.zeq_expr.zexpr_desc with
    | Z_tuple(el) -> el
    | _ -> [equs.zeq_expr]
  in
  (* D'abord une étape de traitement *)
  let patterns, expressions =
    normalize
      node
      patts
      exprs
  in
  (* Puis la construction des formules *)
  List.map2 (build_formula node)
    patterns
    expressions

  
(** Build_zexpr:
    Créée une z_expr avec une z_expr_desc et une t_expr
    Pratique
    @params:            
    @return:
 **)
let build_zexpr (ze: z_expr_desc) (te: TE.t_expr) =
  {zexpr_desc=ze;
   zexpr_type=te.texpr_type;}    



  
(** Propagate_convert:
    
    @params:            
    @return:
 **)
let rec propagate_convert (te: TE.t_expr) =
  debugging debug (fun () -> Printf.printf "    Propagate_convert\n");
  match te.texpr_desc with
  | TE.TE_const(c) -> Z_const(c)
  | TE.TE_ident(id) -> Z_ident(id)
  | TE.TE_pre(e) ->
     let e' = (propagate_convert e) in
     let ze =
       build_zexpr e' e in
     Z_pre(ze)
  | TE.TE_arrow(e1, e2) ->
     let e1' = (propagate_convert e1) in
     let e2' = (propagate_convert e2) in
     let ze1, ze2 = (build_zexpr e1' e1), (build_zexpr e2' e2) in
     Z_arrow(ze1, ze2)
     
  | TE.TE_op(op, el) ->
     let new_op, el' =
       match op with
       | Op_gt ->
          Comparator(Op_lt), (List.rev el)           
       | Op_ge ->
          Comparator(Op_le), (List.rev el)
       | Op_eq | Op_neq
         | Op_lt | Op_le -> Comparator(op), el

       | Op_add | Op_sub
         | Op_mul | Op_div
         | Op_add_f | Op_sub_f
         | Op_mul_f | Op_div_f
         | Op_mod -> Calculator(op), el

       | Op_not | Op_and
         | Op_or | Op_xor | Op_impl ->
          Combinator(op), el

       | Op_if ->
          Branchment(op), el  
     in
     let zl =
       List.map propagate_convert el' in
     let new_list =
       List.map2 build_zexpr zl el in
     Z_op(new_op, new_list)
     
  | TE.TE_app(id, el) ->
     let zl =
       List.map propagate_convert el in
     let new_list =
       List.map2 build_zexpr zl el in
     Z_app(id, new_list)
     
  | TE.TE_prim(id, el) ->
     let zl =
       List.map propagate_convert el in
     let new_list =
       List.map2 build_zexpr zl el in
     Z_prim(id, new_list)
     
  | TE.TE_tuple(el) ->
     let zl =
       List.map propagate_convert el in
     let new_list =
       List.map2 build_zexpr zl el in
     Z_tuple(new_list)
     

(** Convert: Fonction qui convertie les Op_ge et Op_gt en Op_le et Op_lt
    De plus elle convertie tout les opérateurs en catégories:     
    Calculateur|Comparateur|Combinateur|Branchement. 
    @params:            
    @return:
 **)
let convert
      (node: z_node)
      (eq: TE.t_equation)
    : z_equation
  =
  debugging debug (fun () -> (Printf.printf "<Convert>\n"));
  { zeq_patt=eq.teq_patt;
    zeq_expr={ zexpr_desc=propagate_convert eq.teq_expr;
               zexpr_type=eq.teq_expr.texpr_type }; }


(** Generate_aez_node:Fonction qui génère un
    Aez Node qui contient la liste des formules pour
    la vérification.
    
    @params:            
    @return:
 **)
let generate_aez_node (tnode : Typed_ast.t_node) =
  debugging debug (fun () -> (Printf.printf "\n    <Ast_to_astaez>: "));
  debugging debug (fun () -> (Printf.printf "Node=%s\n" tnode.tn_name.name));
  
  let (node: z_node) =
    { z_name = tnode.tn_name;
      node_input = [];
      node_output = [];
      node_vlocal = [];
      node_equs = [];
      node_loc = tnode.tn_loc;
      symboles = Iota.empty;
    }
  in   
  let input  = (* DONE *)
    List.map (var_aez node) tnode.tn_input in
  let output = (* DONE *)
    List.map (var_aez node) tnode.tn_output in  
  let local  = (* DONE *)
    List.map (var_aez node) tnode.tn_local in
  
  (* Printf.printf "Liste des patterns:\n";
   * List.iter (fun (eq: Typed_ast.t_equation) ->
   *     List.iter (fun (patt: Ident.t) -> Printf.printf "%s\n" patt.name) eq.teq_patt.tpatt_desc) tnode.tn_equs; *)

  let zequs = List.map (convert node) tnode.tn_equs in
  (* PARTIALLY DONE *)
  let equs = 
    List.flatten (List.map (equs_aez node) zequs) in
  incr id_sym;
  
  debugging debug (fun () -> (Printf.printf "    Liste des elements de Iota:\n"));
  debugging debug (fun () -> (Iota.iter
                                (fun k e -> Printf.printf "      --> %s , %s\n" (k.name)
                                              (Hstring.view e))
                                node.symboles));
  
  { node with
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
  }

  
(** Aezfify: Crée un nouvel arbre de syntaxe
    après une éventuelle normalisation.
    
    @param:
    @return: Un enregistrement représantant
             le noeud et ses formules dans le format
             attendu par le module Aez.
 **)
let aezdify (ast_node: TE.t_node list) =
  debugging debug (fun () -> (Printf.printf "<Aezdify> begin\n"));
  let laez = List.map generate_aez_node ast_node in
  debugging debug (fun () -> (Printf.printf "<Aezdify> end\n"));
  laez
    

    (* TODO LIST :

     - Fonction Normalize convert & propagate_convert :
       Trouver un moyen de construire une z_expr (sous fonctions)
       pour garder le match.

     - Faire remonter les types pour finir le débug.

     *)
