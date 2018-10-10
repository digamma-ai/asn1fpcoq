open OcamlFPBER

let () =
  let _ = ocaml_float64_to_BER_exact Float.neg_infinity in
  Printf.eprintf "*** Test!\n" ;
  exit 0
