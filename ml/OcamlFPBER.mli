open Binary
open Big_int

val ocaml_float64_to_BER_exact: big_int -> bool -> float -> string option

val ocaml_BER_to_float64_exact: string -> float option

val ocaml_BER_to_float64_rounded: mode -> string -> float option
