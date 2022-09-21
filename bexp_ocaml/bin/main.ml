open Bexp_ocaml
open Bexp_ocaml.Lexer
open Lexing

let evaluate expr =
  let lexbuf = Lexing.from_string expr in
  match Parser.prog Lexer.read lexbuf with
  | Some value ->
    let parsed = Util.string_of_boolexp value in
    Printf.printf "Parsed term: %s\n" parsed;

    let result = Core.BoolExp.bigstep_ex value |> Util.string_of_boolexp in
    Printf.printf "Result: %s\n" result;
  | None -> ()

let () = evaluate "if (if true then false else true) then true else (if true then false else true)"; ()
