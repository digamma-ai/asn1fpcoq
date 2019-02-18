open Asn1fp
open OUnit2
open Big_int
open Core

open FullBin

let opt_float_eqb_nan_t o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some f1, Some f2 -> f1 = f2 || (Float.is_nan f1 && Float.is_nan f2)
  | _, _ -> false

let roundtrip radix scaled f =
  match ocaml_float64_to_BER_exact radix scaled f with
  | None -> None
  | Some a ->
     let mf = ocaml_BER_to_float64_exact a in
     match mf with
     | None -> None
     | Some _ -> mf

let test_no_scl_radix2 v _ =
  assert_equal ~cmp:opt_float_eqb_nan_t
    ~printer:(fun so -> match so with
                        | None -> "None"
                        | Some s -> string_of_float s)
    (Some v) (roundtrip (big_int_of_int 2) false v)

let normal_numbers_suite =
  "Normal Numbers">:::
    List.map
      [3.1415; (-3.1415); 3E12; 96.0]
      ~f:(fun v -> string_of_float v >:: test_no_scl_radix2 v)

let special_values_suite =
  "Special Values">:::
    ["+Zero" >:: test_no_scl_radix2 0.0;
     "-Zero" >:: test_no_scl_radix2 (-0.0);
     "+Inf"  >:: test_no_scl_radix2 Float.infinity;
     "-Inf"  >:: test_no_scl_radix2 Float.neg_infinity;
     "NaN"   >:: test_no_scl_radix2 Float.nan]

let positive_numbers_suite n =
  "Postivie Numbers">:::
    List.map (List.range 0 n ) ~f:(fun _ ->
        let v = Random.float Float.max_finite_value in
        string_of_float v >:: test_no_scl_radix2 v)

let _ =
  run_test_tt_main
    ("All tests" >:::[
       normal_numbers_suite;
       positive_numbers_suite 1000;
       special_values_suite])
