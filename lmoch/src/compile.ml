open Asttype


exception Compilation_Terminated of int

let compile_input i =
  let s =
    match i with
    | (x, ty) ->
       begin
         match ty with
         | Tbool -> sprintf "bool %s;\n" "bool" x
         | Tint -> sprintf "int %s;\n" "int" x
         | Treal -> sprintf "float %s" x
         | _ -> failwith "compile::compile_input::Type non reconnu"
       end
    | _ -> failwith "compile::compile_input::Type attendu : Ident.t * Asttypes.base_ty"
  in
  s

let compile_node n =
  let fname = sprintf "%s" n.tn_name.name in
  let inames = sprintf "(%s)" (String.concat compile_input n.tn_input) in
  fprint fmt fname;
  List.iter (fprintf fmt) vnames;
  failwith "compile::compile_node::Under Implementation"




let rec compile astt =
  match astt with
  | [] -> raise (Compilation_Terminated 0)
  | n::reste -> compile_node n; compile reste
