open OcamlFPBER
open Big_int

let ocaml_float64_to_BER (f: float): string option = 
  ocaml_float64_to_BER_exact (big_int_of_int 2) false f

let () =
  Callback.register "ocaml_double_to_ber" ocaml_float64_to_BER;
  Callback.register "ocaml_ber_to_double" ocaml_BER_to_float64_exact;
;;