Require Import ZArith Zdigits.
Require Import ASN.ASNDef ASN.ASNCalc Aux.Option Conversion.ASN_IEEE.
Require Import Program.Basics.

Require Import Flocq.Core.Digits Flocq.Core.Zaux.

Section Basic_structure.

  Let BER_REAL_IDENTIFIER := 9%Z.

  (*
    same as Zdigits2,
    only considering the number 0
    as needing 1 bit to be encoded
  *)
  Definition Zbits (n : Z) : Z :=
    match n with
    | Z0 => 1
    | Zpos p => Zdigits2 (Zpos p)
    | Zneg p => Zdigits2 (Zpos p)
    end.

  Definition Zoctets (n : Z) : Z :=
    (Zbits n + 7) / 8.

  (*
    given two numbers [fst] and [snd] representing two bit strings,
    concatentate them, placing [snd] in a string of [bits_snd] bits

    e.g.
      join_bits 2 3 5 = 67 ( = 10 00011)
   *)
  Let join_bits (fst snd : Z) (bits_snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  Example jb_2_3_5_67 : join_bits 2 3 5 = 67%Z.
  Proof. reflexivity. Qed.

  (*
    concatenate two numbers,
    encoding the second one in exactly
    the smallest number of octets
    that is enough to represent it

    e.g.
      join_octets 2 257 = 131329 (= 10 00000001 00000001)
  *)
  Definition join_octets (fst snd : Z) :Z :=
    join_bits fst snd (8 * (Zoctets snd)).

  Example jo_2_257_131329 : join_octets 2 257 = 131329%Z.
  Proof. reflexivity. Qed.

  Infix "+o+" := join_octets (at level 100, right associativity).

  (*
    given the three main blocks of any BER encoding,
    create the BER bit string
  *)
  Let join_BER_bits (id len content : Z) : Z :=
    id +o+ len +o+ content.

  (*
    given the content block of a BER real encoding,
    create the full bit string
    (add indentifier and inferred content length)
  *)
  Let make_BER_real_bits (content : Z) : Z :=
    join_BER_bits BER_REAL_IDENTIFIER (Zoctets content) content.

  Let BER_radix2Z (b : radix) : Z := Z.log2 b - 1.

  Definition BER_binary_real_descriptor
             (sign radix scaling_factor exp_octets : Z) : Z :=
    let bin_sign               := join_bits 1 sign 1 in
    let bin_sign_radix         := join_bits bin_sign radix 2 in
    let bin_sign_radix_scaling := join_bits bin_sign_radix scaling_factor 2 in
    join_bits bin_sign_radix_scaling exp_octets 2.

  (*
    given the sign, radix, mantissa and exponent of a BER float
    generate the content block of that float
  *)
  Definition make_BER_finite_real_content_no_scl (s : bool) (b : radix) (m : positive) (e : Z) :=
    let Zm := Zpos m in
    let e_octets := Zoctets e in
    let twos_e := Z.of_nat (octet_twos_complement e) in
    let long_exp := (Z.gtb e_octets 3) in
    let descriptor := if long_exp
                      then BER_binary_real_descriptor (bit_value s) (BER_radix2Z b) 0 3
                      else BER_binary_real_descriptor (bit_value s) (BER_radix2Z b) 0 (e_octets-1)
    in
    if long_exp
    then descriptor +o+ e_octets +o+ twos_e +o+ Zm
    else descriptor +o+ twos_e +o+ Zm.

  (* REAL SPECIAL VALUES *)
  Let BER_PLUS_ZERO_BITS := (* 8.1.3.4 : length octet; 8.5.2 : content octet*)
    join_octets BER_REAL_IDENTIFIER 0.
  Let BER_MINUS_ZERO_BITS :=
    make_BER_real_bits 131.
  Let BER_PLUS_INFINITY_BITS :=
    make_BER_real_bits 128.
  Let BER_MINUS_INFINITY_BITS :=
    make_BER_real_bits 129.
  Let BER_NOT_A_NUMBER_BITS :=
    make_BER_real_bits 130.

  (* encoding a BER float as a bit-string *)
  Definition bits_of_BER (f : BER_float) : Z :=
    match f with
    | BER_zero s => if s then BER_MINUS_ZERO_BITS else BER_PLUS_ZERO_BITS
    | BER_infinity s => if s then BER_MINUS_INFINITY_BITS else BER_PLUS_INFINITY_BITS
    | BER_nan => BER_NOT_A_NUMBER_BITS
    | BER_finite s b m e _ => make_BER_real_bits (make_BER_finite_real_content_no_scl s b m e)
    end.

  (* decoding a bit string to a BER float *)
  Definition BER_of_bits : Z -> option BER_float.
  Admitted.

  (* the meaningless function *)
  Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
    := compose Some.

  (* equality on BER_float *)
  Definition BER_eq_b : BER_float -> BER_float -> bool.
  Admitted.

  (*
    for any BER_float,
    if it can be encoded as a bit string (which it can, see `Some_ize_always_some`)
    then
        it can be decoded
      and
        the result is equal to the starting float
  *)
  Theorem BER_bits_BER_roundtrip (f : BER_float) :
    roundtrip
      BER_float Z BER_float
      (Some_ize bits_of_BER)
      (BER_of_bits)
      BER_eq_b
      f.
  Admitted.

End Basic_structure.


Section Aux.

  Theorem bits_of_BER_decodable :
    forall f : BER_float, is_Some_b (BER_of_bits (bits_of_BER f)) = true.
  Admitted.

  Theorem Some_ize_always_some :
    forall (A B : Type) (f : A -> B) (a : A),
      is_Some_b ((Some_ize f) a) = true.
  Proof.
    intros A B f a.
    reflexivity.
  Qed.

End Aux.