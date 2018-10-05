Require Import ZArith Bool.
Require Import Aux.Roundtrip Aux.Tactics Aux.StructTactics.
Require Import Flocq.Core.Digits.

Require Import Lia.

Open Scope Z_scope.

Section Length.

  (* number of base-2 digits of the absolute value of an integer *)
  Definition blen (n : Z) : Z :=
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
  Definition blen_to_olen (n : Z) : Z :=
    (n + 7) / 8.

  (*
    smallest number of octets enough
    to encode a given number in binary
    (workaround for division with rounding toward +inf)
  *)
  Definition olen (n : Z) : Z :=
    blen_to_olen (blen n).

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
  Definition twos_blen (z : Z) : Z :=
    match z with
      | Z0 => 1
      | Zpos zp => (blen z) + 1
      | Zneg zp => 
        let zz := Zpos zp in
        if Zeq_bool zz (2 ^ (Z.log2 zz))
        then (blen zz)
        else (blen zz) + 1
    end.

  (*
    smallest number of octets enough to
    encode an integer's two's complement.
  *)
  Definition twos_olen (z : Z) : Z :=
    blen_to_olen (twos_blen z).

  (* TODO: good description *)
  Definition twos_complement (b : Z) (n : Z) : Z :=
    let r := 2^(b-1) in
    if (Z.gtb n 0)
    then
      if (Z.gtb n (r - 1))
         then n - 2*r
         else n
    else n + 2*r.

    Definition twos_comp_extended (b : Z) (n : Z) : Z :=
    let r := 2^(b-1) in
    let dr := 2*r in
    if (b <? 0)
    then n
    else if (n <? -r)
         then n
         else if n <? 0
              then n + dr
              else if n <? r
                   then n
                   else if n <? dr
                        then n - dr
                        else n.

    Lemma twos_comp_extended_roundtrip (b : Z) (n : Z) :
      bool_het_inverse
        Z Z Z
        (twos_comp_extended b)
        (twos_comp_extended b)
        Z.eqb
        n.
    Proof.
      unfold bool_het_inverse, twos_comp_extended.
      remember (2^(b-1)) as r.
      repeat break_match;
        try rewrite Z.ltb_lt in *;
        try rewrite Z.ltb_nlt in *;
        rewrite Z.eqb_eq in *;
        lia.
    Qed.





  Definition twos_comp (b : Z) (n : Z) : Z :=
    if (Z.geb n 0)
    then n
    else n + 2^b.

  Definition untwos_comp (b : Z) (n : Z) : Z :=
    let r := 2^b in
    if Z.ltb n (r/2)
    then n
    else n - r.

  Lemma twos_comp_inv (b : Z) (n : Z) :
    let r := 2^b in
       Z.ltb 0 b
    && Z.ltb (-r/2 - 1) n
    && Z.ltb n (r/2) = true ->
    bool_het_inverse
      Z Z Z
      (twos_comp b)
      (untwos_comp b)
      Z.eqb
      n.
  Proof.
    (*
    intros r H. subst r. repeat split_andb. rewrite Z.ltb_lt in *.
    unfold bool_het_inverse.
    unfold twos_comp, untwos_comp.
    break_match. remember (2^b) as r.
    rewrite Z.ltb_lt in Heqb0.
    rewrite Z.eqb_eq.
    - break_match.
      + reflexivity.
      + 
    *)
  Admitted.

       













  (*
    calculate two's complement of an integer [z]
    on a given number of octets
  *)
  Definition octet_twos_complement (o : Z) (n : Z) : Z :=
    twos_complement (8*o) n.

  Theorem twos_comp_inv' (b n : Z) :
    let r := (2^(b-1))%Z in
    Z.gtb b 1 = true ->
    Z.gtb n (- r) = true ->
    Z.gtb (r - 1) n = true ->
    bool_het_inverse
      Z Z Z
      (twos_complement b)
      (twos_complement b)
      Z.eqb
      n.
  Proof.
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
    join_bits fst snd (8 * (olen snd)).

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
    split_bits_by_snd b ((blen b) - bits_fst).

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
    split_octets_by_snd b (olen b - octets_fst).

End Operations.