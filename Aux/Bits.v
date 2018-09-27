Require Import ZArith.
Require Import Flocq.Core.Digits.

  (*
    how many digits does a binary representation
    of a given number have
  *)
  Definition Zbits (n : Z) : Z :=
    match n with
    | Z0 => 1
    | Zpos p => Zdigits2 (Zpos p)
    | Zneg p => Zdigits2 (Zpos p)
    end.

  (*
    smallest number of octets enough
    to encode a given number in binary
    (workaround for division with rounding toward +inf)
  *)
  Definition Zoctets (n : Z) : Z :=
    (Zbits n + 7) / 8.

  Definition twos_complement (b : Z) (n : Z) : Z :=
    let r := (2^b)%Z in
    if (Z.gtb n 0)
    then
      if (Z.gtb n (r/2 - 1))
         then n - r
         else n
    else n + r.


  Lemma twos_complement_inv (b : Z) (n : Z) :
    Z.gtb n (- 2^(b-1)) = true ->
    Z.ltb n (2^b - 1) = true ->
    Z.eqb (twos_complement b (twos_complement b n)) n = true.
  Admitted.

  (*
    given two numbers [fst] and [snd] representing two bit strings,
    concatentate them, using [bits_snd] bits to represent [snd] 
   *)
  Definition join_bits (fst snd : Z) (bits_snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  (*
    concatenate two numbers, encoding the [snd] in exactly
    the smallest number of octets that is enough to represent it
  *)
  Definition join_octets (fst snd : Z) :Z :=
    join_bits fst snd (8 * (Zoctets snd)).

  (*
    split a string of bits [b] into two,
    with the right part having length of [bits_snd] bits
  *)
  Definition split_bits_by_snd (b : Z) (bits_snd : Z) : Z * Z :=
    let d := Zpower 2 bits_snd in
    (Z.div b d, Zmod b d).

  (*
    split a string of bits [b] into two,
    with the left part having length of [bits_fst] bits
  *)
  Definition split_bits_by_fst (b : Z) (bits_fst : Z) : Z * Z :=
    split_bits_by_snd b ((Zbits b) - bits_fst).

  (*
    split a string of bits [b] into two,
    with the right part having length of [octets_snd] octets
  *)
  Definition split_octets_by_snd (b : Z) (octets_snd : Z) : Z * Z :=
    split_bits_by_snd b (8 * octets_snd).

  (*
    split a string of bits [b] into two,
    with the left part having length of [octets_snd] octets

    NOTE: 
      if overall number of bits is not divisible by 8, leading zeros are assumed:
      the right part of the split always has a number of bits divisible by 8
      For example:
            110011001111 -> 00001100  11001111,
        NOT 110011001111 -> 11001100  1111
  *)
  Definition split_octets_by_fst (b : Z) (octets_fst : Z) : Z * Z :=
    split_octets_by_snd b (Zoctets b - octets_fst).