open Asttype


exception Compilation_Terminated of int

  

let compile_node n =
  let s1 = sprintf "%s" n.name.name in
  let s2 = sprintf "%s" 




let rec compile astt =
  match astt with
  | [] -> raise (Compilation_Terminated 0)
  | n::reste -> compile_node n; compile reste
