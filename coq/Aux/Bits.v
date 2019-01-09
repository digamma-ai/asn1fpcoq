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
   *  (workaround for division with rounding toward +inf)
   *)
  Definition olen_of_blen (n : Z) : Z :=
    (n + 7) / 8.

  (*
   *  smallest number of octets enough
   *  to encode a given number in binary
   *)
  Definition olen (n : Z) : Z :=
    olen_of_blen (blen n).

End Length.

Section Twos_comp_def.

  (*
   * all definitions assume
   * b bits, number n
   *)
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
    olen_of_blen (twos_blen).

  (*
   * two's complement of n on b bits if possible
   * n if impossible
   *)
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

  Definition twos_dom :=
    negb (b <? 0) && (-r - 1 <? n) && (n <? r).
  Definition twos_ran :=
    negb (b <? 0) && (-1 <? n) && (n <? dr).

  (* some useful subsets of twos_comp_extended's domain: *)
  (* "left" *)
  Definition twos_l :=
    negb (b <? 0) && (- r - 1 <? n) && (n <? 0).
  (* "middle" *)
  Definition twos_m :=
    negb (b <? 0) && (-1 <? n) && (n <? r).
  (* "right" *)
  Definition twos_r :=
    negb (b <? 0) && (r - 1 <? n) && (n <? dr).

End Twos_comp_def.

Section Twos_comp_proof.

  (* from "left", twos_comp_extended always brings to "right" *)
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
  
  (* from "middle", twos_comp_extended always brings to "middle" *)
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
  
  (* from "right", twos_comp_extended always brings to "left" *)
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

End Twos_comp_proof.

Section Split_concat.

  (*
   *  given two numbers [fst] and [snd] representing two bit strings,
   *  concatentate them, using [bits_snd] bits to represent [snd] 
   *)
  Definition join_bits_ext (bits_snd : Z) (fst snd : Z) : Z :=
    (Z.shiftl fst bits_snd + snd)%Z.

  (*  concatenate [fst] and [snd], with no leading zeroes in [snd] *)
  Definition join_bits (fst snd : Z) : Z :=
    join_bits_ext (blen snd) fst snd.

  (*
   *  given two numbers [fst] and [snd] representing two bit strings,
   *  concatentate them, using [octets_snd] octets to represent [snd] 
   *)
  Definition join_octets_ext (octets_snd : Z) (fst snd : Z) : Z :=
    join_bits_ext (8 * octets_snd) fst snd.

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
   *    if overall number of bits is not divisible by 8, leading zeros assumed:
   *    the right part of the split always has a number of bits divisible by 8
   *    For example:
   *          110011001111 -> 00001100  11001111,
   *      NOT 110011001111 -> 11001100  1111
   *)
  Definition split_octets_by_fst (octets_fst : Z) (b : Z) : Z * Z :=
    split_octets_by_snd (olen b - octets_fst) b.

  Lemma split_join_bits (bits_snd fst snd : Z) :
    0 <= snd ->
    blen snd <= bits_snd ->
    split_bits_by_snd bits_snd (join_bits_ext bits_snd fst snd) = (fst, snd).
  Proof.
    unfold blen, split_bits_by_snd, join_bits_ext.
    intros H0 H00.
    generalize (Z.log2_nonneg snd); intros.
    assert (0 < 2) by lia.
    assert (0 < bits_snd) by lia.
    assert (0 <= bits_snd) by lia.
    generalize (Z.pow_pos_nonneg 2 bits_snd H1 H3); intros.
    assert (Z.log2 snd < bits_snd) by lia.
    rewrite Z.shiftl_mul_pow2 by (apply H3).
    remember (2^bits_snd) as s.
    replace (fst * s + snd) with (snd + fst * s) by lia.
    rewrite Z.div_add by lia.
    rewrite Z.mod_add by lia.
    assert (H000 : 0 < snd \/ 0 = snd) by lia.
    destruct H000 as [H000 | ]; [ | subst; auto ].
    assert (snd < s) by (apply (Z.log2_lt_pow2 snd bits_snd H000) in H5; lia).
    rewrite Z.div_small by lia.
    rewrite Z.mod_small by lia.
    auto.
  Qed.
    
  Lemma Zdiv_pinf_ge (a b : Z) :
    0 < b ->
    a <= b * ((a + (b - 1)) / b).
  Proof.
    intros.
    rewrite (Z_div_mod_eq a b).
    destruct (a mod b) eqn:H1.
    - (* b | a *)
      rewrite Z.add_0_r.
      replace (b * (a / b) + (b - 1)) with ((b - 1) + (a / b) * b) by lia.
      rewrite Z_div_plus by lia.
      rewrite Z.mul_add_distr_l.
      rewrite (Z.div_small (b - 1) b) by lia.
      lia.
    - remember (Z.pos p) as k; assert (0 < k) by lia; clear Heqk p.
      replace (b * (a / b) + k + (b - 1)) with (k + (b - 1) + (a / b) * b) by lia.
      rewrite Z_div_plus by lia.
      rewrite Z.mul_add_distr_l.
      (* k < a, so strong induction would help *)
      assert (k <= (b * ((k + (b - 1)) / b))) by admit.
      lia.
    - exfalso.
      generalize (Z_mod_lt a b); lia.
  Admitted.
    
  Lemma split_join_octets (octets_snd fst snd : Z) :
    0 <= snd ->
    olen snd <= octets_snd ->
    split_octets_by_snd octets_snd (join_octets_ext octets_snd fst snd) = (fst, snd).
  Proof.
    intros.
    unfold olen, olen_of_blen in H0.
    unfold split_octets_by_snd, join_octets_ext.
    apply split_join_bits.
    apply H.
    remember (blen snd) as b.
    apply Z.mul_le_mono_nonneg_l with (p := 8) in H0; [| lia].
    assert (b <= 8 * ((b + 7) / 8))
      by (replace 7 with (8 - 1) by trivial; apply Zdiv_pinf_ge; lia).
    lia.
  Qed.

  Lemma join_bits_blen (bits_snd fst snd : Z) :
    0 <= fst -> 0 <= snd ->
    blen snd <= bits_snd ->
    blen (join_bits_ext bits_snd fst snd) <= (blen fst) + bits_snd.
  Proof.
    unfold join_bits_ext, blen.
    intros.
    assert (0 <= bits_snd) by
      (assert (0 <= Z.log2 snd) by apply Z.log2_nonneg; lia).
    rewrite Z.shiftl_mul_pow2; [| apply H2].
    assert(0 = fst \/ 0 < fst) by lia; clear H; destruct H3.
    - (* fst = 0 *)
      subst; rewrite Z.mul_0_l, Z.add_0_l; generalize (Z.log2_nonpos 0); intros; lia.
    - (* fst > 0 *)
    assert (Z.log2 (fst * 2 ^ bits_snd + snd) = Z.log2 (fst * 2 ^ bits_snd)).
    {
      assert(0 = snd \/ 0 < snd) by lia; clear H0; destruct H3.
      - subst. rewrite Z.add_0_r. reflexivity.
      - rewrite Z.log2_mul_pow2 by lia.
        generalize (Z.log2_lt_pow2 snd bits_snd H0); intros.
        assert (snd < 2 ^ bits_snd) by lia; clear H3.
        remember (2^bits_snd) as sb.
        assert (fst * sb + snd < (fst + 1) * sb) by lia.
        assert (fst + 1 <= 2*fst) by lia.
        apply Z.mul_le_mono_nonneg_r with (p := sb) in H5; [|lia].
        assert (fst * sb + snd < 2 * fst * sb) by lia.
        clear H3 H5.
        admit.
    }
    rewrite Z.log2_mul_pow2 in H3 by lia.
    lia.
  Admitted.
  
End Split_concat.