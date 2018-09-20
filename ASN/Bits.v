Require Import ZArith.
Require Import ASN.ASNDef ASN.ASNCalc Aux.Option Conversion.ASN_IEEE.
Require Import Program.Basics.

Require Import Flocq.Core.Digits Flocq.Core.Zaux.

Section Basic_structure.

  (* real special values *)
  (* 00001001 *)
  Let BER_REAL_IDENTIFIER := 9%Z.
  (* 01000000 *)
  Let BER_PLUS_INFINITY := 128%Z.
  (* 01000001 *)
  Let BER_MINUS_INFINITY := 129%Z.
  (* 01000010 *)
  Let BER_NOT_A_NUMBER := 130%Z.
  (* 01000011 *)
  Let BER_MINUS_ZERO := 131%Z.


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

  (*
    given two numbers [fst] and [snd] representing two bit strings,
    concatentate them, placing [snd] in a string of [bits_snd] bits

    e.g.
      join_bits 2 3 5 = 67 ( = 10 00011)
   *)
  Definition join_bits (fst snd : Z) (bits_snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  Definition join_bits_safe (fst snd : Z) (bits_snd : Z) : option Z :=
    if Z.gtb (Zbits snd) bits_snd
    then None
    else Some (Z.shiftl fst bits_snd + snd)%Z.

  Definition Zsign (s : bool) : Z :=
    match s with
    | true => 0%Z
    | false => 1%Z
    end.

  Definition BER_binary_real_descriptor (s : bool) (r : radix) (scl : Z) (el : Z) : Z :=
    join_bits
      (join_bits
        (join_bits
          (Zsign s)
          (radix_val r)
          2)
      scl
      2)
    el
    2.
  
  (* encoding a BER float in a bit-string *)
  Definition bits_of_BER : BER_float -> Z.
  Admitted.

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
