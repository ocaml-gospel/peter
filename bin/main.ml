open Gospel2cfml
open Gospel
open Format

let fname = ref None
let version = "0.1~dev"

let spec =
  [
    ( "--version",
      Arg.Unit
        (fun () ->
          printf "gospel2cfml %s@." version;
          exit 0),
      " print version information" );
  ]

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
  let file_cfml = Sep2coq.sep_defs file_sep in
  let out_fname = file_sep.fmodule ^ "_mli.v" in
  let base_dir =
    "/home/tiago/phd/cfml/examples/translations/" ^ file_sep.fmodule
  in
  let () =
    if not (Sys.file_exists base_dir) then Sys.mkdir base_dir 0o755 else ()
  in
  let directory = base_dir ^ "/" ^ out_fname in

  let fmt = formatter_of_out_channel (open_out directory) in
  fprintf fmt "%s@." (Print_coq.tops (file_cfml ~stdlib:true))
