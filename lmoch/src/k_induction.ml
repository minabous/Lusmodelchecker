open Aez
open Smt
open Transform_aez

exception BASE_CASE_FALSE
exception TRUE_PROPERTY
exception FALSE_PROPERTY




module BMC_solver = Smt.Make(struct end)
module IND_solver = Smt.Make(struct end)

  
let induction kprim nodes ({tn_input; tn_output; tn_local; tn_equs} as node)=
   try 
(*cas de base ∆(0) , ∆(1) ......|= P(0)∧P(1).......P(K)  *)
    Format.printf"Prooving the base case\n"

     for i=0 to kprim-1 do
      BMC_solver.assume ~id:0 (delta_incr i);
     done;
      BMC_solver.check();
       
    for i=0 to kprim-1 do 
      if not(BMC_solver.entails ~id:0 (ok i)) then raise (Base_Case_Fails );
     done;

(*cas de base ∆(n) , ∆(n+1) ...P(n),P(n+1)...P(n+k)|= P(n+k+1)  *)

let induct k =
  let n = Term.make_app (declare_symbol "n" [] Type.type_int) [] in
    Format.printf"Prooving the inductive case\n"
    for(i =0 to kprim ) do 
   IND_solver.assume ~id:0 (delta_incr i);
    if(i < kprim) then 
     Kind_solver.assume ~id:0 (Formula.make_lit Formula.Lt [Term.make_int (Num.Int kprim); n]);

     if(i>0)
      then begin
       
     end

    IND_solver.check() ;

  if not (Inductive_solver.entails ~id:0 (ok )) then raise (False_Property)


end;

   TRUE_PROPERTY

  with
    |False_Property  ->  Format.printf "FALSE PROPERTY";
   
    |Base_Case_Fails ->   Format.printf "FALSE PROPERTY";


















