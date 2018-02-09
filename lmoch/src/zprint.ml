open Asttypes
open Ident


   
let match_op = (fun o -> match o with Op_eq -> "eq"
                                     |Op_neq -> "neq"
                                     |Op_lt -> "lt"
                                     |Op_le -> "le"
                                     |Op_add|Op_add_f  -> "+"
                                     |Op_sub|Op_sub_f -> "-"
                                     |Op_mul|Op_mul_f -> "*"
                                     |Op_div|Op_div_f -> "/"
                                     |Op_if ->"if")
                
let print_expr_Zop op sym =
  Printf.printf "%s = TE_op(%s, _)\n" sym.name
    (match_op op)





