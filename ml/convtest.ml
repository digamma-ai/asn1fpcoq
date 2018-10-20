open OcamlFPBER

let pr_hexstring = String.iter (fun c -> Printf.eprintf "%02X " (Char.code c))

let test_roundtrip f =
  match ocaml_float64_to_BER_exact f with
  | None -> Printf.eprintf "FP->BER Conversion error of %f!\n" f ; None
  | Some a ->
     Printf.eprintf "FP->BER Conversion of %f produced %d BER bytes: [ " f (String.length a) ;
     pr_hexstring a ;
     Printf.eprintf "]\n" ;
     let mf = ocaml_BER_to_float64_exact a in
     begin
       match mf with
       | None -> Printf.eprintf "FP->BER->FP Conversion back error for %f!\n" f
       | Some f' -> Printf.eprintf "After converting %f got back: %f\n" f f'
     end;
     mf

let () =
  Printf.eprintf "Testing...\n" ;
  let _ = test_roundtrip 3.1415 in
  let _ = test_roundtrip (1E2) in
  let _ = test_roundtrip (-3E9) in
  let _ = test_roundtrip Float.neg_infinity in
  let _ = test_roundtrip Float.nan in
  exit 0
