open OcamlFPBER
open OUnit2
open Big_int

let float_eqb_nan_t f1 f2 =
  f1 = f2 || (Core.Float.is_nan f1 && Core.Float.is_nan f2)

let roundtrip radix scaled f =
  match ocaml_float64_to_BER_exact radix scaled f with
  | None -> None
  | Some a ->
     let mf = ocaml_BER_to_float64_exact a in
       match mf with
       | None -> None
       | Some _ -> mf

let r2 = big_int_of_int 2

(*
let test_no_scl_radix2 f = assert_equal
  (Core.Option.map2 (Some f) (roundtrip r2 false f) float_eqb_nan_t)
  (Some true)
*)
let test_no_scl_radix2 f _ = assert_equal
  (match (roundtrip r2 false f) with
  | None -> false
  | Some f' -> float_eqb_nan_t f f')
  true

let normal_numbers_suite =
  "Normal Numbers">:::
    List.map (fun v -> string_of_float v >:: test_no_scl_radix2 v)
      [3.1415; (-3.1415); 3E12]

let special_values_suite =
"Special Values">:::
  ["+Zero">:: test_no_scl_radix2 0.0;
  "-Zero">:: test_no_scl_radix2 (-0.0);
  "+Inf">:: test_no_scl_radix2 Float.infinity;
  "-Inf">:: test_no_scl_radix2 Float.neg_infinity;
  "NaN">:: test_no_scl_radix2 Float.nan]


let _ =
  run_test_tt_main
    ("All tests" >:::[
      normal_numbers_suite ;
      special_values_suite])
