(* Programme principal *)

open Format
open Lexing
open Lexer
open Parser
open Parse_ast
open Typed_aez

let usage = "usage: "^Sys.argv.(0)^" [options] file.lus <main>"

let parse_only = ref false
let type_only = ref false
let norm_only = ref false
let lucy_printer = ref false
let ocaml_printer = ref true
let verbose = ref false
let debug = ref false
let induction = ref 1
  
let spec =
  ["-parse-only", Arg.Set parse_only, "  stops after parsing";
   "-type-only", Arg.Set type_only, "  stops after typing";
   "-norm-only", Arg.Set norm_only, "  stops after normalization";
   "-verbose", Arg.Set verbose, "  print intermediate transformations";
   "-debug", Arg.Set debug, "  print debug informations for aez transformations";
   "-d", Arg.Set debug, "  print debug informations for aez transformations";
   "-v", Arg.Set verbose, "  print intermediate transformations";
   "-ind", Arg.Set_int induction, "  manualy set the level on induction";
   
  ]

let file, main_node =
  let file = ref None in 
  let main = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".lus") then
      raise (Arg.Bad "no .lus extension");
    file := Some s
  in
  let set_main s =
    main := Some s
  in
  let cpt = ref 0 in
  let set s =
    incr cpt;
    match !cpt with
    | 1 -> set_file s
    | 2 -> set_main s
    | _ -> raise (Arg.Bad "Too many arguments")
  in
  Arg.parse (Arg.align spec) set usage;
  (match !file with Some f -> f | None -> Arg.usage spec usage; exit 1),
  (match !main with Some n -> n | None -> Arg.usage spec usage; exit 1)

let report_loc (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

(****fonction pour tester le type de sortie********)

let check_type  (outs: z_var list ) =
match outs with    
  | [] -> raise (Invalid_argument "outs ")
  | [out] -> (snd out) = Asttypes.Tbool;
     
  |o1::os ->List.for_all (fun o1 -> snd o1=Asttypes.Tbool) outs
    



let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.token lb in
    close_in c;
    if !parse_only then exit 0;
    let ft = Typing.type_file f main_node in
    if !verbose then begin
      Format.printf "/****************************************/@.";
      Format.printf "|*               Typed ast              *|@.";
      Format.printf "/****************************************/@.";
      Typed_ast_printer.print_node_list_std ft;
      (* Printf.printf "In the mood\n"; *)
      end;
    if !type_only then exit 0;
    if main_node = "" then exit 0;
    (* XXX TODO XXX *)
    Incr_proof.check();
    let ftz = Transform_aez.aezdify ft in
    let l = List.length ftz in
    Printf.printf "Nombre de Nodes dans la liste : %d\n" l;
    for k=0 to l-1 
    do
      let z_node = List.nth ftz k in
      Printf.printf "Node courant: %s\n" z_node.z_name.Ident.name;
      if z_node.z_name.Ident.name = main_node then
        begin
          if check_type z_node.node_output then 
            K_induction.check z_node (!induction + 1)
          else
            Printf.printf "Type bool attendu : Pass\n"
        end
      else
        Printf.printf "Node attendu : %s\n" main_node
    done;
    (* XXX TODO XXX *)    
    exit 0
  with
    | Lexical_error s ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "lexical error: %s\n@." s;
	exit 1
    | Parsing.Parse_error ->
	report_loc (lexeme_start_p lb, lexeme_end_p lb);
	eprintf "syntax error\n@.";
	exit 1
    | Typing.Error(l,e) ->
	report_loc l;
	eprintf "%a\n@." Typing.report e;
	exit 1
    | e ->
        eprintf "Anomaly: %s\n@." (Printexc.to_string e);
        exit 2
