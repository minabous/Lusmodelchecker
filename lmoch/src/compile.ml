open Asttype


exception Compilation_Terminated of int

  

let compile_node n =
  let s1 =  




let rec compile astt =
  match astt with
  | [] -> raise (Compilation_Terminated 0)
  | n::reste -> compile_node n; compile reste
