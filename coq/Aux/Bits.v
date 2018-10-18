Require Import ZArith Bool.
Require Import ASN1FP.Aux.Roundtrip ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics.

Require Import Lia.

Open Scope Z_scope.

(* base-2 logarithm rounded toward positive infinity *)
Definition log2_pinf (n : Z) : Z :=
  let ln := Z.log2 n in
  if (n =? 2^ln)
  then ln
  else ln + 1.

Section Length.

  (*
   *  number of base-2 digits of an integer :
   *  n is b bits
   *  <->
   *  2^(b-1) <= n < 2^b
   *  <->
   *  b-1 <= log2 n < b
   *  <->
   *  floor (log2 n) = b - 1
   *  <->
   *  b = floor (log2 n) + 1
   *)
  Definition blen (n : Z) : Z :=
    Z.log2 n + 1.

  (*
   *  smallest number of octets,
   *  which can fit a given number of bits:
   *  
   *  number of bits divided by 8
   *  rounded toward positive infinity
   *)
  Definition blen_to_olen (n : Z) : Z :=
    (n + 7) / 8.

  (*
   *  smallest number of octets enough
   *  to encode a given number in binary
   *  (workaround for division with rounding toward +inf)
   *)
  Definition olen (n : Z) : Z :=
    blen_to_olen (blen n).

End Length.

Section Twos_comp_def.

  Variable b n : Z.
  Let r := 2^(b-1).
  Let dr := 2*r.

  (*
   *  smallest number of bits enough to
   *  encode an integer's two's complement
   * 
   *  when given b bits, two's complement representation
   *  can encode integer values in the range
   *  [-2^(b-1), 2^(b-1)-1].
   *
   *
   *  cosider 3 cases:
   *
   *  1) n = 0 :
   *     twos_blen 0 = 1
   *
   *  2) n > 0 :
   *     n <= 2^(b-1)-1 <-> n < 2^(b-1)
   *
   *         twos_blen n = b
   *     <-> 2^(b-2) <= n < 2^(b-1)
   *     <-> floor (log2 n) = b - 2
   *     <-> b = floor (log2 n) + 2
   *
   *  3) n < 0 :
   *         twos_blen n = b
   *     <-> -2^(b-1) <= n < -2^(b-2)
   *     <-> 2^(b-2) < n <= 2^(b-1)
   *     <-> ceil (log2 (-n)) = b - 1
   *     <-> b = ceil (log2 (-n)) + 1
   *)
  Definition twos_blen : Z :=
    match n with
      | Z0 => 1
      | Zpos _ => Z.log2 n + 2
      | Zneg _ => log2_pinf (- n) + 1
    end.

  (*
   *  smallest number of octets enough to
   *  encode an integer's two's complement.
   *)
  Definition twos_olen : Z :=
    blen_to_olen (twos_blen).

  Definition twos_comp_extended : Z :=
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

  Definition twos_l :=
    negb (b <? 0) && (- r - 1 <? n) && (n <? 0).

  Definition twos_m :=
    negb (b <? 0) && (-1 <? n) && (n <? r).

  Definition twos_r :=
    negb (b <? 0) && (r - 1 <? n) && (n <? dr).

  Definition twos_dom :=
    negb (b <? 0) && (-r - 1 <? n) && (n <? r).

  Definition twos_ran :=
    negb (b <? 0) && (-1 <? n) && (n <? dr).

End Twos_comp_def.

Section Twos_comp_prop.

    Lemma twos_comp_l_ran (b n : Z) :
      twos_l b n = true ->
      twos_r b (twos_comp_extended b n) = true.
    Proof.
      unfold twos_l, twos_r, twos_comp_extended.
      remember (2^(b-1)) as r.
      assert (R: 0 <= r). { subst. apply (Z.pow_nonneg 2). lia. }
      intros H; repeat split_andb.
      repeat break_match; split_andb_goal;
        try rewrite Z.ltb_ge in *; rewrite Z.ltb_lt in *;
          try lia;
            inversion H; inversion H1.
    Qed.

    Lemma twos_comp_m_ran (b : Z) (n : Z) :
      twos_m b n = true ->
      twos_m b (twos_comp_extended b n) = true.
    Proof.
      unfold twos_m, twos_m, twos_comp_extended.
      remember (2^(b-1)) as r.
      assert (R: 0 <= r). { subst. apply (Z.pow_nonneg 2). lia. }
      intros H; repeat split_andb.
      repeat break_match; split_andb_goal;
        try rewrite Z.ltb_ge in *; rewrite Z.ltb_lt in *;
          try lia;
            inversion H; inversion H1.
    Qed.

    Lemma twos_comp_r_ran (b : Z) (n : Z) :
      twos_r b n = true ->
      twos_l b (twos_comp_extended b n) = true.
    Proof.
      unfold twos_r, twos_l, twos_comp_extended.
      remember (2^(b-1)) as r.
      assert (R: 0 <= r). { subst. apply (Z.pow_nonneg 2). lia. }
      intros H; repeat split_andb.
      repeat break_match; split_andb_goal;
        try rewrite Z.ltb_ge in *; rewrite Z.ltb_lt in *;
          try lia;
            inversion H; inversion H1.
    Qed.

    Lemma twos_blen_untwos (b : Z) (n : Z) :
      (n >? 0) &&
      twos_ran b n = true ->
      twos_blen (twos_comp_extended b n) = blen n + 1.
    Proof.
      unfold twos_ran, twos_comp_extended, twos_blen, blen, log2_pinf.
      remember (2^(b-1)) as r.
      assert (R: 0 <= r). { subst. apply (Z.pow_nonneg 2). lia. }
      intros H; repeat split_andb.

      repeat break_match;
        try rewrite Z.ltb_ge in *; rewrite Z.ltb_lt in *;
          try lia.

      - subst n. inversion H0.
      - subst n. inversion H0.
      - inversion H2.
      - inversion H1.
      - subst n. remember (Z.pos p) as n. lia.
      - subst n. remember (Z.pos p) as n. lia.
      - admit.
      - admit.
    Abort.


    Lemma twos_olen_untwos (o : Z) (n : Z) :
      let b := 8*o in
      twos_ran b n = true ->
      twos_olen (twos_comp_extended b n) <= olen n.
    Proof.
    Admitted.

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

End Twos_comp_prop.


Section Operations.

  (*
   *  given two numbers [fst] and [snd] representing two bit strings,
   *  concatentate them, using [bits_snd] bits to represent [snd] 
   *)
  Definition join_bits_ext (bits_snd : Z) (fst snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  Definition join_bits (fst snd : Z) : Z :=
    join_bits_ext (blen snd) fst snd.

  Definition join_octets_ext (snd_olen : Z) (fst snd : Z) : Z :=
    join_bits_ext (8 * snd_olen) fst snd.

  (*
   *  concatenate two numbers, encoding the [snd] in exactly
   *  the smallest number of octets that is enough to represent it
   *)
  Definition join_octets (fst snd : Z) : Z :=
    join_octets_ext (olen snd) fst snd.

  (*
   *  split a string of bits [b] into two,
   *  with the right part having length of [bits_snd] bits
   *)
  Definition split_bits_by_snd (bits_snd : Z) (b : Z) : Z * Z :=
    let d := (2^bits_snd)%Z in
    (Z.div b d, Zmod b d).

  (*
   *  split a string of bits [b] into two,
   *  with the left part having length of [bits_fst] bits
   *)
  Definition split_bits_by_fst (bits_fst : Z) (b : Z) : Z * Z :=
    split_bits_by_snd ((blen b) - bits_fst) b.
  (*
   *  split a string of bits [b] into two,
   *  with the right part having length of [octets_snd] octets
   *)
  Definition split_octets_by_snd (octets_snd : Z) (b : Z) : Z * Z :=
    split_bits_by_snd (8 * octets_snd) b.

  (*
   *  split a string of bits [b] into two,
   *  with the left part having length of [octets_snd] octets
   *
   *  NOTE: 
   *    if overall number of bits is not divisible by 8, leading zeros are assumed:
   *    the right part of the split always has a number of bits divisible by 8
   *    For example:
   *          110011001111 -> 00001100  11001111,
   *      NOT 110011001111 -> 11001100  1111
   *)
  Definition split_octets_by_fst (octets_fst : Z) (b : Z) : Z * Z :=
    split_octets_by_snd (olen b - octets_fst) b.

End Operations.