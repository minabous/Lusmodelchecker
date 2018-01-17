open Asttype
open Astc
exception Enf_of_List
exception Compilation_Terminated of int

let compile_var i =
  let s =
    match i with
    | (x, ty) ->
       begin
         match ty with
         | Tbool -> sprintf "bool %s;\n" x
         | Tint -> sprintf "int %s;\n" x
         | Treal -> sprintf "float %s" x
         | _ -> failwith "compile::compile_input::Type non reconnu"
       end
    | _ -> failwith "compile::compile_input::Type attendu : Ident.t * Asttypes.base_ty"
  in
  s

let rec construe code name =
  let c_code =
    match code with
      begin
      | [] -> raise End_of_List
      | s :: tl ->
         match s with
         | Name(name) -> start_struct name
         | Ivar(var) -> compile_var var
         | Ovar(var) -> compile_var var
         | Lvar(var) -> compile_var var
         | Step(ivl, ov) ->
         | Reset -> 
      end
  in
  List.fold_left
end


let start_struc name =
  sprintf "typedef %s %s" name open_bracket

let start_struc name =
  sprintf "%s %s;" close_bracket name
  
let compile_node n =
  let fname =  Node_Name(n.tn_name.name) in
  let inames = List.map translate_input n.tn_input in
  let onames = List.map translate_output n.tn_output in
  let lnames = List.map translate_local n.tn_local in
  let step = create_step n in
  let reset = create_reset n in
  let code =
    (start_struc fname)@open_bracket
    @inames
    @onames
    @lnames
    @close_bracket
    @(end_struct fname)in
  construe code;
  List.iter (fprintf fmt) code
  
  failwith "compile::compile_node::Under Implementation"


    
let rec compile astt =
  match astt with
  | [] -> raise (Compilation_Terminated 0)
  | n::reste -> compile_node n; compile reste
