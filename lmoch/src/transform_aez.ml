open Aez
open Smt
open Num
open Typed_aez
open Asttypes
   
module TE = Typed_ast

let i = ref 0
  
let declare_symbol (node: z_node) (v: Ident.t) t_in t_out =
  let x = Hstring.make v.name in
  Symbol.declare x t_in t_out;
  node.symboles <- Iota.add v x node.symboles;
  Printf.printf "(%s, %s)\n" v.name (Hstring.view x)

let declare_symbol_ws (node: z_node) (v: String.t) t_in t_out =
  let x = Hstring.make v in
  Symbol.declare x t_in t_out;
  Printf.printf "(%s, %s)\n" v (Hstring.view x);
  x

let var_aez (node: z_node) (input : TE.typed_var)
    : TE.typed_var  =
  Printf.printf "    <Var_aez>\n";
  match input with
  | (v, ty) ->
     Printf.printf "    Nom des variables+Hstring:  ";
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
let rec formula_of
          node
          (expr: z_expr_desc)
          n =
  Printf.printf "Formula_of\n";
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
       match el with
       | [e1; e2] ->
          let e1, e2 = e1.zexpr_desc, e2.zexpr_desc in
          begin
            match op with
            | Comparator(o) ->
               Formula.make_lit (compare o)
                 [ term_of node e1 n;
                   term_of node e2 n ]  
            | Combinator(o) ->
               Formula.make (logic o)
                 [ formula_of node e1 n;
                   formula_of node e2 n ]             
            | _ ->
               failwith "transform_aez::formula_of::Operator expression has to be bool"
          end
     end
    
  | _ ->
     failwith "transform_aez::formula_of::Not Implemeted"
    
(* let e1, e2 = List.nth el 0, List.nth el 1 in
 * Formula.make (logic op) formula_of *)     
(* *************************** AEZ_term ************************** *)
and term_of node (expr: z_expr_desc) n =
  Printf.printf "Term_of\n";  
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
               Printf.printf "Z_op nbr d'opérandes : %d\n" (List.length el);
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
               Printf.printf "Op_if nbr de branches : %d\n" (List.length el);
               failwith "transform_aez::term_of::Three expressions expected"
          end
       | Combinator(o) | Comparator(o) ->
          failwith (Printf.sprintf "transform_aez::term_of::
                                    [Operator=%s] : Expected an operator of type Calculator or Branchment" (Zprint.match_op o))  
     end
    
  | Z_arrow (e1 ,e2) ->
     let e1, e2 = e1.zexpr_desc, e2.zexpr_desc in
     Term.make_ite
       (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
       (term_of node e1 n)
       (term_of node e2 n)

  (* let ty1, ty2 = (List.hd e1.ty), (List.hd e2.ty) in
      * match ty1, ty2 with
      * | Tint, Tint
      *   |Treal, Treal ->
      *    let e1, e2 = e1.zexpr_desc, e2.zexpr_desc in
      *    Term.make_ite
      *      (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
      *      (term_of node e1 n)
      *      (term_of node e2 n)
      * | Tbool, Tbool ->
      *    let e1, e2 = e1.zexpr_desc, e2.zexpr_desc in
      * Term.make_ite
      *   (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
      *   (term_of node e1 n)
      *   (term_of node e2 n) *)
        
     
  | Z_pre(e) ->
     let e = e.zexpr_desc in
     term_of node e (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)))    
     
  | _ ->
     failwith "transform_aez::term_of::Not implemented"
    
    
let make_formula
      (node: z_node)
      (sym: Ident.t)
      (expr: z_expr_desc)
      (n: Term.t) =
  Printf.printf "<Make_formula>\n";
  Printf.printf "sym=%s\n" sym.name;
  let formula =
    match expr with
    | Z_const(c) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_const(_)\n" (Hstring.view hsym);

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_ident(id) ->
       let hsym = Iota.find sym node.symboles in
       let hvar = Iota.find id node.symboles in
       Printf.printf "%s = TE_ident(%s)\n" (Hstring.view hsym) (Hstring.view hvar);
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           Term.make_app hvar [n] ]

    | Z_op (Comparator(op), el) ->
       (* Probleme ici Hstring view doit etre remplacé par un Ident.t pour que ça marche ...*)

       let zexpr_list =
         [ { zexpr_desc=Z_ident(sym);
             zexpr_type=[Tbool];};
           { zexpr_desc=Z_const(Cbool(true));
             zexpr_type=[Tbool];} ]
       in
       let expr_aux = Z_op(Comparator(Op_eq), zexpr_list) in
       let aux_n = formula_of node expr_aux n in
       Zprint.print_expr_Zop op sym;
       
       Formula.make Formula.And
         [ Formula.make Formula.Imp [ aux_n; formula_of node expr n ] ;
           Formula.make Formula.Imp [ formula_of node expr n; aux_n ] ]
       
    | Z_op ((Calculator(op)
             | Combinator(op)
            | Branchment(op)), el) ->
       let hsym = Iota.find sym node.symboles in
       Zprint.print_expr_Zop op sym;

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           term_of node expr n]
       
    | Z_arrow(_, _) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_arrow(_, _)\n" sym.name;
       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n];
           term_of node expr n ]
       
    | Z_pre(_) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_pre(_)\n" (Hstring.view hsym);

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_prim(id, el) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_prim(%s, _)\n" (Hstring.view hsym) id.name;

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_tuple(_) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_tuple(_)\n" (Hstring.view hsym);

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | Z_app(id, _) ->
       let hsym = Iota.find sym node.symboles in
       Printf.printf "%s = TE_app(%s, _)\n" (Hstring.view hsym) id.name;

       Formula.make_lit Formula.Eq
         [ Term.make_app hsym [n]; term_of node expr n ]
       
    | _ -> failwith "transform_aez::make_formula::List match expressions not implemented"
  in
  (* let fmt =
   *   Format.make_formatter
   *     (Pervasives.output_substring Pervasives.stdout)
   *     (fun () -> Pervasives.flush Pervasives.stdout)
   * in *)
  Smt.Formula.print Format.std_formatter formula;
  print_newline();
  formula
  
  
(* Eventuellement faire cette transformation 
 avant en créant un asttyped_aez pour ensuite parcourir une seul listes. *)
let create_couple_var_ty
      (node: z_node)
      (var:Ident.t)
      (ty: Asttypes.base_ty)
  =
  Printf.printf "    <Create_couple_var_ty>\n";
  (var, ty)
  

(*  *)
let build_formula
      (node: z_node)
      (patt_ty: Ident.t * Asttypes.base_ty)
      (expr: z_expr) =
  Printf.printf "    <Build_formula>\n";
  let var_symbol = fst patt_ty in
  (fun (n: Term.t) -> make_formula node var_symbol expr.zexpr_desc n)

(* *   * *)
let normalize
      (node: z_node)
      (patts: (Ident.t * Asttypes.base_ty) list)
      (exprs: z_expr list) =
  Printf.printf "    <Normalize>\n";
  let rec aux acc1 acc2
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
                 let fresh_var = id, Asttypes.Tbool
                 in
                 (* S'il y a moyen de récupérer la valeur finale à
                    la fin du parsing alors initialiser i 
                    avec cette valeur + 1 *)

                 let (fresh_expr:z_expr) =
                   {                   
                     zexpr_desc=Z_ident(id);
                     zexpr_type=[Asttypes.Tbool];
                   }
                 in
                 (* Condenser le code du haut dans une fonction
                  * de cette configuration:
                  * let id, fresh_var, expr = generate_fresh_var *)
                 incr i;
                 aux (acc1@[a]@[fresh_var])
                   (acc2@[fresh_expr]@[b])
                   tla tlb
              | _ -> aux (acc1@[a]) (acc2@[b]) tla tlb
            end
         (* | Z_arrow(e1, e2) ->
          *    begin
          *      let ty1, ty2 = (List.hd e1.ty), (List.hd e2.ty) in
          *      match ty1, ty2 with
          *      | Tbool, Tbool ->
          *         let (id: Ident.t) = 
          *           {
          *             id=(!i);
          *             name=(Printf.sprintf "aux%d" !i);
          *             kind=Ident.Stream;
          *           }
          *         in
          *         declare_symbol node id
          *           [Type.type_int]
          *           Type.type_bool;
          *         let fresh_var = id, Asttypes.Tbool in
          *         aux (acc1@[a]) (acc2@[b]) (::tla) (tlb)
          *         
          *      | _, _ -> aux (acc1@[a]) (acc2@[b]) tla tlb
          *    end *)

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
let equs_aez (node:z_node) (equs: z_equation) =
  Printf.printf "\n<Equs_aez>\n";
  let vars = equs.zeq_patt.tpatt_desc in
  let tys = equs.zeq_patt.tpatt_type in
  let patts = List.map2 (create_couple_var_ty node) vars tys in
  let exprs =
    match equs.zeq_expr.zexpr_desc with
    | Z_tuple(el) -> el
    | _ -> [equs.zeq_expr]
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

let build_zexpr (ze: z_expr_desc) (te: TE.t_expr) =
  {zexpr_desc=ze;
   zexpr_type=te.texpr_type;}    


let rec propagate_convert (te: TE.t_expr) =
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
         | Op_or | Op_impl -> Combinator(op), el

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
     
(* Fonction converte convertie les ge et gt en le et lt
   De plus elle convertie tout les opérateur en catégories:
   Calculateur|Comparateur|Combinateur|Branchement.          
 *)
let convert
      (node: z_node)
      (eq: TE.t_equation)
    : z_equation
  =
  Printf.printf "<Convert>\n";
  { zeq_patt=eq.teq_patt;
    zeq_expr={ zexpr_desc=propagate_convert eq.teq_expr;
               zexpr_type=eq.teq_expr.texpr_type }; }
  
let ast_to_astaez (tnode : Typed_ast.t_node) =
  Printf.printf "    <Ast_to_astaez>: ";
  Printf.printf "Node=%s\n\n" tnode.tn_name.name;
  let (node: z_node) =
    { node_name = tnode.tn_name;
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

  Printf.printf "    Liste des elements de Iota:\n";
  Iota.iter
    (fun k e -> Printf.printf "      --> %s , %s\n" (k.name)
                  (Hstring.view e))
    node.symboles;
  
  { node with
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
  }

  
(* ********************************************************************** *)
(** aezfify: Crée un nouvel arbre de syntaxe
    après une éventuelle normalisation.
    
    @param:
    @return: Un enregistrement représantant
             le noeud et ses formules dans le format
             attendu par le module Aez.
 **)
let aezdify (ast_node: TE.t_node list) =
  Printf.printf "<Aezdify> begin\n";
  let laez = List.map ast_to_astaez ast_node in
  Printf.printf "<Aezdify> end\n";
  laez







    (* TODO LIST :

     - Fonction Normalize convert & propagate_convert :
       Trouver un moyen de construire une z_expr (sous fonctions)
       pour garder le match.

     - Faire remonter les types pour finir le débug.

     *)
