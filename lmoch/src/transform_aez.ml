open Aez
open Smt
open Num
module F = Formula
module T = Term
open Typed_aez
open Asttypes
   
exception FALSE_PROPERTY
exception TRUE_PROPERTY
exception BASE_CASE_FAILS

module BMC_solver = Smt.Make(struct end) 
module IND_solver = Smt.Make(struct end)

let i = ref 0
      
let declare_symbol (node: z_node) (name: String.t) t_in t_out =
  let x = Hstring.make name in
  Symbol.declare x t_in t_out;
  node.symboles <- Iota.add name x node.symboles;
  Printf.printf "(%s, %s)\n" name (Hstring.view x);
  x
  
let var_aez (node:z_node) (input : Ident.t * Asttypes.base_ty) =
  Printf.printf "    <Var_aez>\n";
  match input with
  | (v, ty) ->
     Printf.printf "    Nom des variables+Hstring:  ";
     match ty with
     | Asttypes.Tbool ->
        (declare_symbol node v.name [Type.type_int] Type.type_bool, ty)
     | Asttypes.Tint  ->
        (declare_symbol node v.name [Type.type_int] Type.type_int, ty)
     | Asttypes.Treal ->
        (declare_symbol node v.name [Type.type_int] Type.type_real, ty)
(* | _ -> failwith "transform_aez::var_aez::Unknown type\n Type Has to be int, bool float" *)
       
       
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
          (node: z_node)
          (expr: Typed_ast.t_expr_desc)
          (n: Term.t) =
  Printf.printf "Formula_of\n";
  match expr with
  | Typed_ast.TE_op(op, el) ->
     match el with
     | [e1; e2] ->
        let e1, e2 = e1.texpr_desc, e2.texpr_desc in
        Formula.make_lit (compare op)
          [ term_of node e1 n;
            term_of node e2 n ]
     | _ ->
        failwith "transform_aez::formula_of::Only two operandes expected"
       
(* let e1, e2 = List.nth el 0, List.nth el 1 in
 * Formula.make (logic op) formula_of *)     
(* *************************** AEZ_term ************************** *)
and term_of (node: z_node) (expr: Typed_ast.t_expr_desc) (n: Smt.Term.t) =
  Printf.printf "Term_of\n";  
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
       | Asttypes.Cint(i) ->  Term.make_int  (Num.Int i)
       | Asttypes.Creal(f) -> Term.make_real (Num.num_of_string (string_of_float f))
     end    
    
  | Typed_ast.TE_ident(id) ->
     let var = Iota.find id.name node.symboles in
     Term.make_app var [n]
     
  | Typed_ast.TE_op(op, el) ->
     begin
       match el with
       | [e1; e2] ->
          let e1, e2 = e1.texpr_desc, e2.texpr_desc in
          Term.make_arith (arith op) (term_of node e1 n) (term_of node e2 n)
       | _ ->
          failwith "transform_aez::term_of::Only two operandes expected"
     end
    
  | Typed_ast.TE_arrow (e1 ,e2) ->
     let e1, e2 = e1.texpr_desc, e2.texpr_desc in
     Term.make_ite
       (Formula.make_lit Formula.Eq [n; Term.make_int (Num.Int 0)])
       (term_of node e1 n)
       (term_of node e2 (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1))))
     
  | Typed_ast.TE_pre(e) ->
     let e = e.texpr_desc in
     term_of node e (Term.make_arith Term.Minus n (Term.make_int (Num.Int 1)))    
     
  | _ ->
     failwith "transform_aez::term_of::Not implemented"

    
let rec make_formula
          (node: z_node)
          (sym: Aez.Hstring.t)
          (expr: Typed_ast.t_expr_desc)
          (n: Term.t) =
  Printf.printf "<Make_formula>\n";
  Printf.printf "expr=%s\n" (Hstring.view sym);
  let formula =
    match expr with
    | Typed_ast.TE_const(c) ->
       Printf.printf "%s = TE_const(_)\n" (Hstring.view sym);
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]
       
    | Typed_ast.TE_ident(id) ->
       let var = Iota.find id.name node.symboles in
       Printf.printf "%s = TE_ident(%s)\n" (Hstring.view sym) id.name;
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n];
           Term.make_app var [n] ]
       
    | Typed_ast.TE_op (op, el) ->
       begin
         match op with
         | Op_eq | Op_neq
           | Op_lt | Op_le
           | Op_gt | Op_ge ->
            let aux_n =
              make_formula node sym (Typed_ast.TE_const (Cbool true)) n
            in
            Printf.printf "%s = TE_op(%s, _)\n"
              (Hstring.view sym)
              ((fun o -> match o with Op_eq -> "eq"
                                     |Op_neq -> "neq"
                                     |Op_lt -> "lt"
                                     |Op_le -> "le") op);
            
            Formula.make Formula.And
              [ Formula.make Formula.Imp [ aux_n; formula_of node expr n ] ;
                Formula.make Formula.Imp [ formula_of node expr n; aux_n ] ]
            
         | Op_add | Op_sub | Op_mul | Op_div | Op_mod
           | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f ->
            Printf.printf "%s = TE_op(%s, _)\n"
              (Hstring.view sym)
              ((fun o -> match o with Op_add|Op_add_f  -> "+"
                                      |Op_sub|Op_sub_f -> "-"
                                      |Op_mul|Op_mul_f -> "*"
                                      |Op_div|Op_div_f -> "/") op);
            
            Formula.make_lit Formula.Eq
              [ Term.make_app sym [n]; term_of node expr n ]
            
         | Op_if  ->
            begin
              match el with
              | [ cond; thn; els ] ->
                 let cond, thn, els =
                   (cond.texpr_desc, thn.texpr_desc, els.texpr_desc) in
                 Printf.printf "%s = TE_op(if, _)\n" (Hstring.view sym);
                 
                 Formula.make_lit Formula.Eq
                   [ Term.make_app sym [n];
                     Term.make_ite
                       (formula_of node cond n)
                       (term_of node thn n)
                       (term_of node els n)
                   ]

              | _ ->
                 failwith "transform_aez::make_formula::Invalid match for IfThenElse"
            end
           
         | _ ->
            failwith "transform_aez::make_formula::Invalid operator"
       end
      
    | Typed_ast.TE_arrow(_, _) ->
       Printf.printf "%s = TE_arrow(_, _)\n" (Hstring.view sym);
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]
       
    | Typed_ast.TE_pre(_) ->
       Printf.printf "%s = TE_pre(_)\n" (Hstring.view sym);
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]
       
    | Typed_ast.TE_prim(id, el) ->
       Printf.printf "%s = TE_prim(%s, _)\n" (Hstring.view sym) id.name;
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]

    | Typed_ast.TE_tuple(_) ->
       Printf.printf "%s = TE_tuple(_)\n" (Hstring.view sym);
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]
       
    | Typed_ast.TE_app(id, _) ->
       Printf.printf "%s = TE_app(%s, _)\n" (Hstring.view sym) id.name;
       Formula.make_lit Formula.Eq
         [ Term.make_app sym [n]; term_of node expr n ]
       
    | _ -> failwith "transform_aez::make_formula::List match expressions not implemented"
  in
  let fmt =
    Format.make_formatter
      (Pervasives.output_substring Pervasives.stdout)
      (fun () -> Pervasives.flush Pervasives.stdout)
  in
  Smt.Formula.print fmt formula;
  formula
  
  
(* Eventuellement faire cette transformation 
 avant en créant un asttyped_aez pour ensuite parcourir une seul listes. *)
let create_couple_var_ty (node: z_node) (var:Ident.t) (ty: Asttypes.base_ty)
    : Aez.Hstring.t * Asttypes.base_ty =
  Printf.printf "    <Create_couple_var_ty>\n";
  (Iota.find var.name node.symboles, ty)


(*  *)
let build_formula
      (node: z_node)
      (patt_ty: Aez.Hstring.t * Asttypes.base_ty)
      (expr: Typed_ast.t_expr) =
  Printf.printf "    <Build_formula>\n";
  let var_symbol = fst patt_ty in
  (fun (n: Term.t) -> make_formula node var_symbol expr.texpr_desc n)

  
(* *   * *)
let normalize
      (node: z_node)
      (patts: (Hstring.t * Asttypes.base_ty) list)
      (exprs: Typed_ast.t_expr list) =
  Printf.printf "    <Normalize>\n";
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
                | Op_not| Op_and
                | Op_or | Op_impl ->
                 let fresh_var =
                   declare_symbol node (Printf.sprintf "aux%d" !i)
                     [Type.type_int]
                     Type.type_bool,
                   Asttypes.Tbool
                 in
                 
                 (* S'il y a moyen de récupérer la valeur finale à
                    la fin du parsing alors initialiser i 
                    avec cette valeur + 1 *)
                 let (id: Ident.t) = 
                   {
                     id=(!i);
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
                 aux (acc1@[a]@[fresh_var])
                   (acc2@[fresh_expr]@[b])
                   tla tlb
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
  Printf.printf "\n<Equs_aez>\n";
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

let convert
      (node: z_node)
      (eq: Typed_ast.t_equation)
  =
  Printf.printf "<Convert>\n";
  match eq.teq_expr.texpr_desc with
  | Typed_ast.TE_op(op, el) ->
     begin
       match op with
       | Op_gt ->
          Printf.printf "Done !\n";
          { eq with
            teq_expr={ eq.teq_expr with
                       texpr_desc=Typed_ast.TE_op(Op_lt, (List.rev el));};}          
       | Op_ge ->
          Printf.printf "Done !\n";
          { eq with
            teq_expr={ eq.teq_expr with
                       texpr_desc=Typed_ast.TE_op(Op_le, (List.rev el));};}
       | _ -> eq
     end
  | _ -> eq
       
let ast_to_astaez (tnode : Typed_ast.t_node) =
  Printf.printf "    <Ast_to_astaez>: ";
  Printf.printf "Node=%s\n\n" tnode.tn_name.name;
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
    List.flatten (List.map (equs_aez node) tnode.tn_equs) in

  Printf.printf "    Liste des elements de Iota:\n";
  Iota.iter
    (fun k e -> Printf.printf "      --> %s , %s\n" (k)
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
let aezdify (ast_node: Typed_ast.t_node list) =
  Printf.printf "<Aezdify> begin\n";
  let laez = List.map ast_to_astaez ast_node in
  Printf.printf "<Aezdify> end\n";
  laez

