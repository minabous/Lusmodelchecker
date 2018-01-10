open Aez


let input_to_aez input =
  match input with
  | (x, ty, _) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::input_to_aez::Not a correct input"
     (*  | _ -> failwith "ast_to_aez::input_to_aez::Not Implemented" *)


let output_to_aez output =
  match output with
  | (x, ty, _) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::output_to_aez::Not a correcte output"


let local_to_aez local =
  match local with
  | (x, ty, _) -> (T_Sym x, ty)
  | _ -> failwith "ast_to_aez::output_to_aez::Not a correcte output"

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


let to_aez ast_node =
  let faez = List.map ast_to_astaez ast_node;
  failwith "ast_to_aez::to_aez::Under Implementation"; 
(* TODO *)    compile_to_alt_ergo faez
