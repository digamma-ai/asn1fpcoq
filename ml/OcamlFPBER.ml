open FullBin
open Core
open String
open Big_int

open BitContainer

let string_of_big_int_bit (x : big_int) : string =
  if eq_big_int x zero_big_int
  then "0"
  else "1"

let big_int_bit_of_string (x : string) : big_int =
  if x = "0"
  then zero_big_int
  else unit_big_int

let rec bits_of_big_int bi =
  let base = big_int_of_int 2 in
  let (q,r) = quomod_big_int bi base in
  let t = string_of_big_int_bit r in
  String.concat [(if eq_big_int q zero_big_int then "" else bits_of_big_int q); t]

let string_of_cont (c : container) : string = bits_of_big_int c

  (*
let rec bytes_of_big_int bi =
  let base = big_int_of_int 256 in
  let (q,r) = quomod_big_int bi base in
  let t = char_of_int (int_of_big_int r) in
  (if eq_big_int q zero_big_int then "" else bytes_of_big_int q)
  ^ of_char t
   *)

let rec big_int_of_bits ?acc:(a=big_int_of_int 0) s =
  let base = big_int_of_int 2 in
  if is_empty s then a
  else
    let x = get s 0 in
    let xs = drop_prefix s 1 in
    let v = (big_int_bit_of_string (String.of_char x)) in
    big_int_of_bits ~acc:((add_big_int (mult_big_int a base) v)) xs

    (*
let rec big_int_of_bytes ?acc:(a=big_int_of_int 0) s =
  let base = big_int_of_int 256 in
  if is_empty s then a
  else
    let x = get s 0 in
    let xs = drop_prefix s 1 in
    let v = big_int_of_int (int_of_char x) in
    big_int_of_bytes ~acc:((add_big_int (mult_big_int a base) v)) xs
     *)

let unsigned_big_int_of_int64 (i:int64) =
  let open Core.Int64 in
  let r = big_int_of_int64 (Int64.max_value) in
  let dr = (mult_big_int (big_int_of_int 2) (succ_big_int r)) in
  if i < Int64.zero
  then add_big_int dr (big_int_of_int64 i)
  else big_int_of_int64 i

let big_int_of_float (f:float) =
  unsigned_big_int_of_int64 (Int64.bits_of_float f)

let int64_of_unsigned_big_int bi =
  let r = big_int_of_int64 (Int64.max_value) in
  let dr = (mult_big_int (big_int_of_int 2) (succ_big_int r)) in
  let open Core in
  if (compare_big_int bi r) > 0
  then int64_of_big_int (sub_big_int bi dr)
  else int64_of_big_int bi

let float_of_big_int fbi =
  Int64.float_of_bits (int64_of_unsigned_big_int fbi)

let ocaml_float64_to_BER_exact (radix:big_int) (scaled:bool) (f:float): String.t option =
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
