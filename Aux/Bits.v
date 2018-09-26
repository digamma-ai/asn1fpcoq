Require Import ZArith.
Require Import Flocq.Core.Digits.

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
  Definition join_bits (fst snd : Z) (bits_snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  Example jb_2_3_5 : join_bits 2 3 5 = 67%Z.
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

  Definition split_bits_by_snd (b : Z) (bits_snd : Z) : Z * Z :=
    let d := Zpower 2 bits_snd in
    (Zdiv b d, Zmod b d).

  Definition split_bits_by_fst (b : Z) (bits_fst : Z) : Z * Z :=
    split_bits_by_snd b ((Zbits b) - bits_fst).

  Definition split_octets_by_snd (b : Z) (octets_snd : Z) : Z * Z :=
    split_bits_by_snd b (8 * octets_snd).

  Definition split_octets_by_fst (b : Z) (octets_fst : Z) : Z * Z :=
    split_octets_by_snd b (Zoctets b - octets_fst).