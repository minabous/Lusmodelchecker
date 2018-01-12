open Parse_ast

type objet =
  | Name of string
  | Ivar of truc
  | Ovar of chose
  | Lvar of machin
  | Step of ceci list
  | Reset of cela list
              
