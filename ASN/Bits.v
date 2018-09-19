Require Import ZArith.
Require Import ASN.ASNDef Aux.Option Conversion.ASN_IEEE.
Require Import Program.Basics.

Section Basic_structure.

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