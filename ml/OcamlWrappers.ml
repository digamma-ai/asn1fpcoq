open OcamlFPBER
open Big_int

let ocaml_float64_to_BER (f: float): string option = 
  ocaml_float64_to_BER_exact (big_int_of_int 2) false f

let () = Printf.printf "This location was reached\n%!"
let () = Callback.register "double_to_ber" ocaml_float64_to_BER
let () = Callback.register "ber_to_double" ocaml_BER_to_float64_exact
