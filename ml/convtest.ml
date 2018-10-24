open OcamlFPBER
open OUnit2
open Big_int

let pr_hexstring = String.iter (fun c -> Printf.eprintf "%02X " (Char.code c))

let float_eqb_nan_t f1 f2 =
  f1 = f2 || (Core.Float.is_nan f1 && Core.Float.is_nan f2)

let r2 = big_int_of_int 2

let roundtrip radix scaled f =
  match ocaml_float64_to_BER_exact radix scaled f with
  | None -> None
  | Some a ->
     let mf = ocaml_BER_to_float64_exact a in
       match mf with
       | None -> None
       | Some _ -> mf

(*
let test_no_scl_radix2 f = assert_equal
  (Core.Option.map2 (Some f) (roundtrip r2 false f) float_eqb_nan_t)
  (Some true)
*)
let test_no_scl_radix2 f = assert_equal
  (match (roundtrip r2 false f) with
  | None -> false
  | Some f' -> float_eqb_nan_t f f')
  true

let normal_numbers_suite =
"Normal Numbers">:::
  ["3.1415">::  (fun _ -> test_no_scl_radix2 3.1415);
   "-3.1415">:: (fun _ -> test_no_scl_radix2 (-3.1415));
   "3T">::      (fun _ -> test_no_scl_radix2 3E12)]

let special_values_suite =
"Special Values">:::
  ["+Zero">:: (fun _ -> test_no_scl_radix2 0.0);
  "-Zero">:: (fun _ -> test_no_scl_radix2 (-0.0));
  "+Inf">:: (fun _ -> test_no_scl_radix2 Float.infinity);
  "-Inf">:: (fun _ -> test_no_scl_radix2 Float.neg_infinity);
  "NaN">:: (fun _ -> test_no_scl_radix2 Float.nan)]

let _ = run_test_tt_main normal_numbers_suite
let _ = run_test_tt_main special_values_suite

(*

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
          if float_eqb_nan_t f f' then
            Printf.eprintf "    PASS: for value %f\n" f
          else
            Printf.eprintf "    FAIL: After converting %f got back: %f!\n" f f'
     end;
     mf

let () =
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
*)
