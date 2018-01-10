open Aez





let input_to_aez in =
  match in with
    |



let ast_to_astaez texpr =
  let name =
    tnode.name in
  let input =
    List.map input_to_aez texpr.tn_input in
  let output =
    List.map output_to_aez texpr.tn_output in
  let local =
    List.map local_to_aez texpr.tn_local in
  let equs =
    List.map equs_to_aez texpr.equs in
  let loc =
    List.map loc_to_aez texpr.tn_loc in
  { name = 
    
  }







let to_aez ast_node =
  let faez = List.map ast_to_astaez ast_node;
  failwith "TODO" 
