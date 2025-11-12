open Gospel2cfml
open Gospel
open Format

let fname = ref None
let version = "0.1~dev"
let stdlib = ref false
let dir = ref ""

type backend = CFML | Iris

let backend = ref CFML

let spec =
  [
    ( "--version",
      Arg.Unit
        (fun () ->
          printf "gospel2cfml %s@." version;
          exit 0),
      " print version information" );
    ( "--iris",
      Arg.Unit (fun () -> backend := Iris),
      " use Iris as a verification backend" );
    ( "--dir",
      Arg.String (fun s -> dir := s),
      " the directory in which the generated file will be output" );
    ( "--stdlib",
      Arg.Unit (fun () -> stdlib := true),
      "Flag to use when translating the Gospel standard library." );
  ]

module Iris = Peter.Make (Peter.Sep_to_iris)

let usage_msg = sprintf "%s <file>.ml\nVerify OCaml program\n" Sys.argv.(0)

let usage () =
  Arg.usage spec usage_msg;
  exit 1

let set_file f =
  match !fname with
  | None when Filename.check_suffix f ".mli" -> fname := Some f
  | _ -> usage ()

let () = Arg.parse spec set_file usage_msg
let fname = match !fname with None -> usage () | Some f -> f

let () =
  let file_sep =
    match Gospel.sep ~verbose:false [ fname ] with
    | [ x ] -> x
    | _ -> assert false
  in

  let file_cfml =
    match !backend with
    | Iris -> Iris.sep_defs ~stdlib:!stdlib file_sep
    | CFML -> assert false
  in

  dir := if not (String.ends_with ~suffix:"/" !dir) then !dir ^ "/" else !dir;
  let base_dir = !dir ^ if !backend = CFML then file_sep.fname ^ "/" else "" in

  let () =
    if base_dir <> "" && not (Sys.file_exists base_dir) then
      Sys.mkdir base_dir 0o755
    else ()
  in
  let oc = open_out (base_dir ^ file_sep.fmodule ^ "_mli.v") in
  let file = Print_rocq.tops file_cfml in
  Out_channel.output_string oc file;
  close_out oc
