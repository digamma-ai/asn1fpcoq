(*open OcamlFPBER

let test_roundtrip f =
  match ocaml_float64_to_BER_exact f with
  | None -> Printf.eprintf "FP->BER Conversion error of %f!\n" f ; None
  | Some a ->
     Printf.eprintf "FP->BER Conversion of %f produced %d BER bytes \n" f (String.length a) ;
     let mf = ocaml_BER_to_float64_exact a in
     begin
       match mf with
       | None -> Printf.eprintf "FP->BER->FP Conversion back error for %f!\n" f
       | Some f' -> Printf.eprintf "After converting %f got back: %f\n" f f'
     end;
     mf
 *)
let () =
(*  let _ = test_roundtrip Float.neg_infinity in
  let _ = test_roundtrip Float.nan in
  let _ = test_roundtrip 3.1415 in *)
  exit 0
