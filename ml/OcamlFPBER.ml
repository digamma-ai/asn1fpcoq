open FullBin
open Core
open String
open Big_int

let r2 = big_int_of_int 2


(* big_int <-> its visual binary representation *)

let string_of_big_int_bit (x : big_int) : string =
  if eq_big_int x zero_big_int
  then "0"
  else "1"

let big_int_bit_of_string (x : string) : big_int =
  if x = "0"
  then zero_big_int
  else unit_big_int

let rec bits_of_big_int bi =
  let base = r2 in
  let (q,r) = quomod_big_int bi base in
  let t = string_of_big_int_bit r in
  String.concat [(if eq_big_int q zero_big_int then "" else bits_of_big_int q); t]

let rec big_int_of_bits ?acc:(a=big_int_of_int 0) s =
  let base = r2 in
  if is_empty s then a
  else
    let x = get s 0 in
    let xs = drop_prefix s 1 in
    let v = (big_int_bit_of_string (String.of_char x)) in
    big_int_of_bits ~acc:((add_big_int (mult_big_int a base) v)) xs

let unsigned_big_int_of_int64 (i:int64) =
  let open Core.Int64 in
  let r = big_int_of_int64 (Int64.max_value) in
  let dr = (mult_big_int (r2) (succ_big_int r)) in
  if i < Int64.zero
  then add_big_int dr (big_int_of_int64 i)
  else big_int_of_int64 i

let big_int_of_float (f:float) =
  unsigned_big_int_of_int64 (Int64.bits_of_float f)

let int64_of_unsigned_big_int bi =
  let r = big_int_of_int64 (Int64.max_value) in
  let dr = (mult_big_int (r2) (succ_big_int r)) in
  let open Core in
  if (compare_big_int bi r) > 0
  then int64_of_big_int (sub_big_int bi dr)
  else int64_of_big_int bi

let float_of_big_int fbi =
  Int64.float_of_bits (int64_of_unsigned_big_int fbi)

let ocaml_float64_to_BER_exact (radix:big_int) (scaled:bool) (f:float): string option =
  let fb = big_int_of_float f in
  match float64_to_BER_exact radix scaled fb with
  | None -> None
  | Some bbi -> Some (bits_of_big_int bbi)

let ocaml_BER_to_float64_exact (ab:string): float option =
  let ai = big_int_of_bits ab in
  match coq_BER_to_float64_exact ai with
  | None -> None
  | Some fbi -> Some (float_of_big_int fbi)





let ocaml_BER_to_float64_rounded (m:Binary.mode) (ab:string): float option =
  let ai = big_int_of_bits ab in
  match coq_BER_to_float64_rounded m ai with
  | None -> None
  | Some fbi -> Some (float_of_big_int fbi)

let string_option_printer (os : string option) : string =
  match os with
  | None -> "None"
  | Some s -> if s = "" then "empty_string" else s

let _ =
  print_endline (string_option_printer (ocaml_float64_to_BER_exact r2 false 96.0))

let ber_cont_of_ocaml_float64 f =
  match (ocaml_float64_to_BER_exact r2 false f) with
  | None -> None
  | Some f' -> Def0.cont_of_BER_bits (big_int_of_bits f')

let cont = ber_cont_of_ocaml_float64 96.0

let _ =
  let b = match cont with
             | None -> None
             | Some c -> Some (bits_of_big_int c) in
  print_endline (string_option_printer b)

open Def0

   (*
let cont_nblen_option (co : cont8 option) =
  match co with
  | None -> None
  | Some c -> Some (coq_BER_nblen c)
    *)

let nbs_of_cont' (co : cont8 option) =
  match co with
  | None -> None
  | Some c -> nbs_of_cont (coq_BER_nblen c) c
  
let _ =
  print_endline (string_option_printer (
  match nbs_of_cont' cont with
  | None -> None
  | Some nbs -> match nbs with
                | Coq_short_nbs (id, co, t, s, bb, ff, ee, e, m) ->
                   Some (String.concat
                                   [
                                     string_of_big_int id;
                                     string_of_big_int co;
                                     string_of_big_int t;
                                     string_of_big_int s;
                                     string_of_big_int bb;
                                     string_of_big_int ff;
                                     string_of_big_int ee;
                                     string_of_big_int e;
                                     string_of_big_int m
                                   ])
                  | Coq_long_nbs (id, co, t, s, bb, ff, ee, eo, e, m) ->
                   Some (String.concat
                                   [
                                     string_of_big_int id;
                                     string_of_big_int co;
                                     string_of_big_int t;
                                     string_of_big_int s;
                                     string_of_big_int bb;
                                     string_of_big_int ff;
                                     string_of_big_int ee;
                                     string_of_big_int eo;
                                     string_of_big_int e;
                                     string_of_big_int m
                                   ])
                   )
    )
