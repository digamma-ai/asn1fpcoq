open Binary

val ocaml_float64_to_BER_exact: float -> string option

val ocaml_BER_to_float64_exact: string -> float option

val ocaml_BER_to_float64_rounded: mode -> string -> float option
