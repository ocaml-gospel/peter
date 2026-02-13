open Gospel2cfml
open Gospel
open Format

let fname = ref None
let version = "0.1~dev"
let file_special = ref Peter.Normal
let dir = ref ""

type backend = CFML | Iris

let backend = ref CFML
let compile = ref true

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
      Arg.Set_string dir,
      " the directory in which the generated file will be output" );
    ( "--special",
      Arg.Symbol
        ( [ "stdlib"; "primitives" ],
          fun s ->
            compile := false;
            match s with
            | "stdlib" -> file_special := Stdlib
            | "primitives" -> file_special := Primitives
            | _ -> assert false ),
      "For developers only. This flag has two settings \"stdlib\" and \
       \"primitives\" which are used when translating the Gospel standard \
       library or the OCaml primitives specification." );
    ("--no-compile", Arg.Unit (fun () -> compile := false), "");
  ]

module Iris = Peter.Make (Peter.Sep_to_iris)
module CFML = Peter.Make (Peter.Sep_to_CFML)

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
let module_suffix = "_mli"
let interface_suffix = module_suffix ^ ".v"
let proof_suffix = "_proof.v"
let project_file = "_CoqProject"

let mk_base base_dir mod_name =
  let oc = open_out (base_dir ^ mod_name ^ proof_suffix) in
  let rocq_mli_module = mod_name ^ module_suffix in
  let proof_file =
    match !backend with
    | CFML -> assert false
    | Iris -> Iris.proof_file rocq_mli_module
  in
  output_string oc proof_file;
  close_out oc;
  let project_file_in_dir = base_dir ^ project_file in
  let oc = open_out project_file_in_dir in
  let rocq_module = Printf.sprintf "-R . %s\n" mod_name in
  let interface = mod_name ^ interface_suffix in
  output_string oc rocq_module;
  output_string oc interface;
  close_out oc;
  let _ =
    Sys.command
      (Printf.sprintf "cd %s && rocq makefile -f %s -o Makefile 1> /dev/null"
         base_dir project_file)
  in
  ()

let () =
  let map = fun x -> x ^ "''" in
  let file_sep =
    match Gospel.sep ~verbose:false ~map [ fname ] with
    | [ x ] -> x
    | _ -> assert false
  in

  let file_cfml =
    match !backend with
    | Iris -> Iris.sep_defs ~special:!file_special file_sep
    | CFML -> CFML.sep_defs ~special:!file_special file_sep
  in

  dir :=
    if (not (String.ends_with ~suffix:"/" !dir)) && !dir <> "" then !dir ^ "/"
    else !dir;
  let base_dir = if !compile then !dir ^ file_sep.fmodule ^ "/" else "" in
  let mk_project = !compile && not (Sys.file_exists base_dir) in
  if mk_project then Sys.mkdir base_dir 0o755;
  let fname = String.uncapitalize_ascii file_sep.fmodule in
  let oc = open_out (base_dir ^ fname ^ interface_suffix) in
  let tops =
    match !backend with
    | Iris -> Print_rocq.Iris.print
    | CFML -> Print_rocq.CFML.print
  in
  let file = tops file_cfml in
  Out_channel.output_string oc file;
  close_out oc;
  if mk_project then mk_base base_dir fname;
  if !compile then
    let _ =
      Sys.command (Printf.sprintf "cd %s && make 1> /dev/null" base_dir)
    in
    ()
