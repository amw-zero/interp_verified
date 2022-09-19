open Bexp_ocaml
open Bexp_ocaml.Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    let parsed = Util.string_of_boolexp value in
    Printf.printf "Parsed term: %s\n" parsed;

    let result = Core.BoolExp.bigstep_ex value |> Util.string_of_boolexp in
    Printf.printf "Result: %s\n" result;
    
    parse_and_print lexbuf
  | None -> ()

let evaluate expr () =
  let lexbuf = Lexing.from_string expr in
  parse_and_print lexbuf

let () = evaluate "if (if true then false else true) then true else (if true then false else true)" ()
