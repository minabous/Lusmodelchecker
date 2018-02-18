open Aez
open Smt
open Num
open Typed_aez
open Asttypes   
module TE = Typed_ast


              
let build_formula node =
  let zexpr = node.node_equs
