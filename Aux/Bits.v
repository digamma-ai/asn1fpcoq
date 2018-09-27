Require Import ZArith.
Require Import Flocq.Core.Digits.

Section Length.

  (* number of base-2 digits of the absolute value of an integer *)
  Definition bits (n : Z) : Z :=
    match n with
    | Z0 => 1
    | Zpos p => Zdigits2 (Zpos p)
    | Zneg p => Zdigits2 (Zpos p)
    end.

  (*
    smallest number of octets,
    which can fit a given number of bits:

    number of bits divided by 8
    rounded toward positive infinity
  *)
  Definition bits_to_octets (n : Z) : Z :=
    (n + 7) / 8.

  (*
    smallest number of octets enough
    to encode a given number in binary
    (workaround for division with rounding toward +inf)
  *)
  Definition octets (n : Z) : Z :=
    bits_to_octets (bits n).

  (* number of base-2 digits of a positive number *)
  Definition bits_Pnat (p : positive) : nat :=
    Z.to_nat (bits (Zpos p)).

  (* smallest number of octets enough to encode a postive number *)
  Definition octets_Pnat (p : positive) : nat :=
    Z.to_nat (bits_to_octets (bits (Zpos p))).

End Length.


Section Twos_complement.

  (*
    smallest number of bits enough to
    encode an integer's two's complement

    when given N bits, two's complement representation
    can encode integer values in the range
    [-2^(N-1), 2^(N-1)-1].
    [twos_bits z] calculates the smallest N
    such that [z] is in that range.
  *)
  Definition twos_bits (z : Z) : Z :=
    match z with
      | Z0 => 1
      | Zpos zp => (bits z) + 1
      | Zneg zp => 
        let zz := Zpos zp in
        if Zeq_bool zz (2 ^ (Z.log2 zz))
        then (bits zz)
        else (bits zz) + 1
    end.

  Definition twos_bits_nat (z : Z) : nat :=
    Z.to_nat (twos_bits z).

  (*
    smallest number of octets enough to
    encode an integer's two's complement.
  *)
  Definition twos_octets (z : Z) : Z :=
    bits_to_octets (twos_bits z).

  Definition twos_octets_nat (z : Z) : nat :=
    Z.to_nat (twos_octets z).

  (* TODO: good description *)
  Definition twos_complement (b : Z) (n : Z) : Z :=
    let r := (2^b)%Z in
    if (Z.gtb n 0)
    then
      if (Z.gtb n (r/2 - 1))
         then n - r
         else n
    else n + r.

  (*
    calculate two's complement of an integer [z]
    on the smallest number of octets possible
  *)
  Definition octet_twos_complement (z : Z) : Z :=
    twos_complement (8 * (twos_octets z)) z.

  Lemma twos_complement_inv (b : Z) (n : Z) :
    Z.gtb n (- 2^(b-1)) = true ->
    Z.ltb n (2^b - 1) = true ->
    Z.eqb (twos_complement b (twos_complement b n)) n = true.
  Admitted.

End Twos_complement.


Section Operations.

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
    join_bits fst snd (8 * (octets snd)).

  (*
    split a string of bits [b] into two,
    with the right part having length of [bits_snd] bits
  *)
  Definition split_bits_by_snd (b : Z) (bits_snd : Z) : Z * Z :=
    let d := (2^bits_snd)%Z in
    (Z.div b d, Zmod b d).

  (*
    split a string of bits [b] into two,
    with the left part having length of [bits_fst] bits
  *)
  Definition split_bits_by_fst (b : Z) (bits_fst : Z) : Z * Z :=
    split_bits_by_snd b ((bits b) - bits_fst).

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
    split_octets_by_snd b (octets b - octets_fst).

End Operations.