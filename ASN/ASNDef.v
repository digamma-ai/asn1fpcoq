Require Import PArith ZArith.
Require Import Flocq.Core.Zaux Flocq.Core.Digits.
(* ISO/IEC 8825-1:2015 *)

(*
  floats encoded in ASN.1 can have base 2,4,8,16
  [ 8.5.7.2 ]
*)
Definition radix4  := Build_radix  4 (refl_equal _).
Definition radix8  := Build_radix  8 (refl_equal _).
Definition radix16 := Build_radix 16 (refl_equal _).

(*
  number of base-2 digits of a positive number
*)
Definition bits (p : positive) : nat :=
  S (digits2_Pnat p).

Example bits_1 : bits 1 = 1.
Proof. reflexivity. Qed.
Example bits_8 : bits 8 = 4.
Proof. reflexivity. Qed.

(*
  smallest number of bits enough to
  encode an integers two's complement

  when given N bits, two's complement representation
  can encode integer values in the range
  [-2^(N-1), 2^(N-1)-1].
  _(twos_bits z)_ calculates the smallest N
  such that _z_ is in that range.
*)
Definition twos_bits (z : Z) : nat :=
  match z with
    | Z0 => 1
    | Zpos zp => (bits zp) + 1
    | Zneg zp => 
      let zz := Zpos zp in

      if Zeq_bool zz (2 ^ (Z.log2 zz))
      then (bits zp)
      else (bits zp) + 1
  end.
                                
Example twos_bits_7 : twos_bits 7 = 4.
Proof. reflexivity. Qed.
Example twos_bits_8 : twos_bits 8 = 5.
Proof. reflexivity. Qed.
Example twos_bits_n8 : twos_bits (- 8) = 4.
Proof. reflexivity. Qed.

(*
  smallest number of octets,
  which can fit a given number of bits:

  number of bits divided by 8
  rounded toward positive infinity
*)
Definition bits_to_octets (n : nat) : nat :=
  (n + 7) / 8.

(*
  smallest number of octets
  enough to encode a postive number
*)
Definition octets (p : positive) : nat :=
  bits_to_octets (bits p).

Example octets_255 : octets 255 = 1.
Proof. reflexivity. Qed.
Example octets_256 : octets 256 = 2.
Proof. reflexivity. Qed.

(*
  smallest number of octets enough to
  encode an integers two's complement.
*)
Definition twos_octets (z : Z) : nat :=
  bits_to_octets (twos_bits z).

Example twos_octets_128 : twos_octets 128 = 2.
Proof. reflexivity. Qed.
Example twos_octets_n128 : twos_octets (- 128) = 1.
Proof. reflexivity. Qed.

Section BER.

(*
  for practical purposes ASN.1 BER floats are encoded in short form
  thus having a limit of
  127 content octets [ 8.1.3.4 ]

  1 of these is used by a standard information octet
  [ 8.5.6 - 8.5.7.4 ]

  126 is left.

  the total number of octets,
  taken up by significand and exponent, needs to be <= 126


  if exponent takes up more than 3 octets,
  an additional octet is required to encode exponent's lenth,
  [ 8.5.7.4 d) ]
  thus the total number of octets,
  taken up by significand and exponent, needs to be <= 125
*)
Definition bounded (m : positive) (e : Z) : bool :=
  let mo := octets m in
  let eo := twos_octets e in
  if 3 <? eo
    then (mo + eo) <=? 125
    else (mo + eo) <=? 126.

(*
  binary radices defined in ASN.1 BER: 2, 4, 8, 16
  [ 8.5.7.2 ]
*)
Definition valid_radix (b : radix) : bool :=
  match (radix_val b) with
  | 2%Z => true
  | 4%Z => true
  | 8%Z => true
  | 16%Z => true
  | _ => false
  end.

(*
  is a given triple (m,e,b)
  (encoding the number m*(b^e))
  in a format accepted by ASN.1 BER
*)
Definition valid_BER (m : positive) (e : Z) (b : radix) : bool :=
  andb (bounded m e) (valid_radix b).
(*
  ASN.1 BER "RealSpecialValues":
  +inf, -inf, NaN, -0
  [ 8.5.9 ]
  
  or finite values
  [8.5.7]
  
  the value "+0" is defined separately in [ 8.5.3 ]
  and, in our scope, shall be treated as a special value
*)
Inductive BER_float :=
  | BER_zero (s : bool)
  | BER_infinity (s : bool)
  | BER_nan
  | BER_finite (s : bool) (b : radix) (m : positive) (e : Z) :
    (valid_BER m e b = true) -> BER_float.

(*
  is the encoding a finite real number
*)
Definition is_finite (r : BER_float) : bool :=
  match r with
  | BER_zero _ => true
  | BER_finite _ _ _ _ _ => true
  | _ => false
  end.

End BER.