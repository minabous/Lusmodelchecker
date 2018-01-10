open Aez


let input_to_aez input =
  match input with
  | (x, ty) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::input_to_aez::Not a correct input"
     (*  | _ -> failwith "ast_to_aez::input_to_aez::Not Implemented" *)


let output_to_aez output =
  match output with
  | (x, ty) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::output_to_aez::Not a correcte output"


let local_to_aez local =
  match local with
  | (x, ty) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::output_to_aez::Not a correcte local variable"

let equs_to_aez equs =
  match equs with
  | _ -> faiwith ""


  
let ast_to_astaez texpr =
  let name =
    tnode.name in
  let input = (* DONE *)
    List.map input_to_aez texpr.tn_input in
  let output = (* DONE *)
    List.map output_to_aez texpr.tn_output in
  let local = (* DONE *)
    List.map local_to_aez texpr.tn_local in
  let equs = (* TODO *)
    List.map equs_to_aez texpr.equs in
  let loc = (* TODO *)
    List.map loc_to_aez texpr.tn_loc in
  { node_name = name;
    node_input = input;
    node_output = output;
    node_vlocal = local;
    node_equs = equs;
    node_loc = loc;
  }



let compile_to_alt_ergo faez =
  
let to_aez ast_node =
  let faez = List.map ast_to_astaez ast_node;
  failwith "ast_to_aez::to_aez::Under Implementation"; 
  (* TODO *)    compile_to_alt_ergo faez;



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
