open OcamlFPBER

let pr_hexstring = String.iter (fun c -> Printf.eprintf "%02X " (Char.code c))

let test_roundtrip radix scaled f =
  Printf.eprintf "Testing for %f\n" f ;
  match ocaml_float64_to_BER_exact radix scaled f with
  | None -> Printf.eprintf "    ERROR: FP->BER Conversion error of %f!\n" f ; None
  | Some a ->
     Printf.eprintf "    FP->BER Conversion of %f produced %d BER bytes: [ " f (String.length a) ;
     pr_hexstring a ;
     Printf.eprintf "]\n" ;
     let mf = ocaml_BER_to_float64_exact a in
     begin
       match mf with
       | None -> Printf.eprintf "    ERROR: FP->BER->FP Conversion back error for %f!\n" f
       | Some f' ->
          let is_nan x = compare x nan = 0 in
          if (f' = f || (is_nan f && is_nan f')) then
            Printf.eprintf "    PASS: for value %f\n" f
          else
            Printf.eprintf "    FAIL: After converting %f got back: %f!\n" f f'
     end;
     mf

let () =
  let open Big_int in
  let r = big_int_of_int 2 in
  let s = false in
  let _ = Printf.eprintf "\n\nTesting finite values\n\n" in
  let _ = test_roundtrip r s (3.1415) in
  let _ = test_roundtrip r s (-3.1415) in
  let _ = test_roundtrip r s (3.0) in
  let _ = test_roundtrip r s (-3.0) in
  let _ = test_roundtrip r s (1E2) in
  let _ = test_roundtrip r s (-3E9) in
  let _ = Printf.eprintf "\nTesting special values\n\n" in
  let _ = test_roundtrip r s (0.0) in
  let _ = test_roundtrip r s (-0.0) in
  let _ = test_roundtrip r s Float.infinity in
  let _ = test_roundtrip r s Float.neg_infinity in
  let _ = test_roundtrip r s Float.nan in
  exit 0
