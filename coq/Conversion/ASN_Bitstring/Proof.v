Require Import ZArith.
Require Import Lia.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits ASN1FP.Aux.Tactics
        ASN1FP.Conversion.ASN_Bitstring.Def.
Require Import Flocq.Core.Zaux.

Open Scope Z.

Section Atomic.

Lemma bits_of_radix_inv (b : radix) : valid_radix b = true ->
  bool_het_inverse
    radix Z radix
    bits_of_radix
    radix_of_bits 
    Z.eqb
    b.
Proof.
  intros H.
  unfold bool_het_inverse, Basics.compose, radix_of_bits, bits_of_radix.
  destruct (Z.eqb b 2) eqn:R2.
  - simpl. apply R2.
  - destruct (Z.eqb b 4) eqn:R4.
    + simpl. apply R4.
    + destruct (Z.eqb b 8) eqn:R8.
      * simpl. apply R8.
      * destruct (Z.eqb b 16) eqn:R16.
        { simpl. apply R16. }
        {
          contradict H.
          unfold valid_radix.
          rewrite R2. rewrite R4. rewrite R8. rewrite R16.
          simpl. auto.
        }
Qed.

Lemma bits_of_sign_inv (s : bool) :
  bool_het_inverse
    bool Z bool
    bits_of_sign
    sign_of_bits
    Bool.eqb
    s.
Proof.
  unfold bool_het_inverse, sign_of_bits, bits_of_sign.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.

 Lemma bits_of_signif_inv (m : positive) :
  bool_het_inverse
	positive Z positive
	bits_of_signif
	signif_of_bits
	Pos.eqb
	m.
Proof.
  unfold bool_het_inverse, signif_of_bits, bits_of_signif.
  simpl. apply Pos.eqb_refl.
Qed.

Lemma bits_of_exp_inv (e_olen e  : Z) :
  bool_het_inverse
    Z Z Z
    (bits_of_exp e_olen)
    (exp_of_bits e_olen)
    Z.eqb
    e.
Proof.
  apply twos_comp_extended_roundtrip.
Qed.

End Atomic.

(*
Compute (
    let e := 999 in
    let eo := 123 in
    orb (negb (andb (Z.leb 0 e) (Z.leb (olen e) eo))) (Z.leb (twos_olen (exp_of_bits eo e)) eo)
  ).
*)

Lemma Zle_lt_or_eq (x y : Z) :
  x <= y ->
  x = y \/ x < y.
Proof. lia. Qed.

Lemma twos_olen_aux (e eo : Z) :
  0 <= e -> 1 <= eo -> olen e <= eo ->
  twos_olen (exp_of_bits eo e) <= eo.
Proof.
  unfold olen, blen, twos_olen, exp_of_bits, olen_of_blen,
    twos_blen, twos_comp_extended, log2_pinf.
  intros Enneg EOpos EO.
  assert (A : 8 <> 0) by lia.
  assert (B : 0 < 2) by lia.
  assert (A1 : 0 < 8) by lia.
  repeat break_match; debool; subst; try lia;
  try (simpl in EO; simpl; apply EO).
  - assert (C : 0 <= 2) by trivial.
    generalize (Z.pow_nonneg 2 (8 * eo - 1) C); intros.
    lia.
  - generalize (Zgt_pos_0 p); intros; apply Z.gt_lt in H.
    remember (Z.pos p) as te.
    remember (Z.log2 te) as lte.
    clear EOpos Heqb0 Heqb1 Heqb Heqte p Enneg.
    replace (lte + 1 + 7) with (lte + 1*8) in EO by lia;
      rewrite (Z.div_add lte 1 8 A) in EO.
    replace (lte + 2 + 7) with (lte + 1 + 1*8) by lia;
      rewrite (Z.div_add (lte + 1) 1 8 A).

    apply (Z.log2_lt_pow2 te (8 * eo - 1) H) in Heqb2.
    rewrite <- Heqlte in Heqb2.
    apply Zsucc_lt_compat in Heqb2.
    replace (Z.succ (8 * eo - 1)) with (8 * eo) in Heqb2 by lia.
    apply (Z.div_lt_upper_bound (lte + 1) 8 eo A1) in Heqb2.
    lia.
  - exfalso.
    generalize (Zgt_pos_0 p); intros; apply Z.gt_lt in H.
    remember (Z.pos p) as te.
    remember (Z.log2 te) as lte.
    clear Heqb0 Heqb1 Heqb2 Heqb Enneg.
    replace (lte + 1 + 7) with (lte + 1*8) in EO by lia;
      rewrite (Z.div_add lte 1 8 A) in EO.
    rewrite <- (Z.pow_succ_r 2 (8 * eo - 1)) in Heqb3 by lia;
      replace (Z.succ (8 * eo - 1)) with (8 * eo) in Heqb3 by lia.
    apply (Z.log2_le_pow2 te (8 * eo) H) in Heqb3.
    rewrite <- Heqlte in Heqb3.
    apply (Z.div_le_lower_bound lte 8 eo A1) in Heqb3.
    lia.
  - remember (- Z.neg p) as te.
    (* care: positiviry of te is lost *) rewrite <- Heqz in Heqte; clear Heqz p.
    clear Heqb0 Heqb1 Heqb2 Enneg.
    remember (Z.log2 e) as le; remember (Z.log2 te) as lte.
    replace (le + 1 + 7) with (le + 1*8) in EO by lia;
      rewrite (Z.div_add le 1 8 A) in EO.
    replace (lte + 1 + 7) with (lte + 1*8) by lia;
      rewrite (Z.div_add lte 1 8 A).
    rewrite <- (Z.pow_succ_r 2 (8 * eo - 1)) in Heqte by lia;
      replace (Z.succ (8 * eo - 1)) with (8 * eo) in Heqte by lia.
    replace (- (e - 2 ^ (8 * eo))) with (2^(8 * eo) - e) in Heqte by lia.
    remember (2^(8 * eo - 1)) as o in *.
    replace (8 * eo) with (Z.succ (8 * eo - 1)) in Heqte by lia.
    rewrite -> Z.pow_succ_r in Heqte by lia.
    rewrite <- Heqo in Heqte.
    assert (H : te <= e) by lia.
    apply Z.log2_le_mono in H.
    rewrite <- Heqle, <- Heqlte in H.
    generalize (Z.div_le_mono lte le 8 A1 H); intros.
    lia.
  - remember (- Z.neg p) as te.
    (* care: positiviry of te is lost *) rewrite <- Heqz in Heqte; clear Heqz p.
    clear Heqb0 Heqb1 Heqb2 Enneg.
    remember (Z.log2 e) as le; remember (Z.log2 te) as lte.
    replace (le + 1 + 7) with (le + 1*8) in EO by lia;
      rewrite (Z.div_add le 1 8 A) in EO.
    replace (lte + 1 + 1 + 7) with (lte + 1 + 1*8) by lia;
      rewrite (Z.div_add (lte + 1) 1 8 A).
    rewrite <- (Z.pow_succ_r 2 (8 * eo - 1)) in Heqte by lia;
      replace (Z.succ (8 * eo - 1)) with (8 * eo) in Heqte by lia.
    replace (- (e - 2 ^ (8 * eo))) with (2^(8 * eo) - e) in Heqte by lia.
    remember (2^(8 * eo - 1)) as o in *.
    replace (8 * eo) with (Z.succ (8 * eo - 1)) in Heqte by lia.
    rewrite -> Z.pow_succ_r in Heqte by lia.
    rewrite <- Heqo in Heqte.
    assert (H : lte + 1 < 8 * eo).
    {
      assert (H : te < o).
      {
        assert (H : te < o \/ te = o) by lia.
        destruct H.
        - apply H.
        - replace o with te in *.
          rewrite Heqo in Heqlte.
          assert (H1 : 0 <= 8 * eo - 1) by lia.
          rewrite (Z.log2_pow2 (8 * eo - 1) H1) in Heqlte.
          rewrite Heqlte in Heqb.
          rewrite Heqo in Heqb.
          lia.
       }
      subst o.
      apply Z.log2_lt_pow2 in H.
      lia.
      lia.
    }
    apply (Z.div_lt_upper_bound (lte + 1) 8 eo A1) in H.
    lia.
Qed.


Lemma valid_short_valid_BER {id co t s bb ff ee e m : Z} :
  valid_short id co t s bb ff ee e m = true ->
  valid_BER
   (radix_of_bits bb) ff (signif_of_bits m) (exp_of_bits (ee + 1) e) = true.
Proof.
  unfold valid_short. intros H.
  repeat split_andb.
  debool.
  clear H0 H12 id t.
  clear H10 H11 s.

  unfold valid_BER. apply andb_true_intro; split; apply andb_true_intro; split.
  - (* bounded *)
    clear H6 H7 ff; clear H8 H9 bb.
    unfold bounded.
    break_match; debool.
    + (* long exponent *)
      apply Z.lt_le_pred; simpl.
      remember (twos_olen (exp_of_bits (ee + 1) e)) as t.
      replace 1 with (Z.succ 0) in H1 by trivial; apply Z.le_succ_l in H1;
        unfold signif_of_bits; rewrite (Z2Pos.id m H1);
        remember (olen m) as om.
      replace (om + ee + 2) with (om + (ee + 1) + 1) in H13 by lia.
        remember (ee + 1) as eo.
      replace ee with (eo - 1) in * by lia; clear Heqeo.
      apply Z.le_sub_le_add_l in H4; simpl in H4.
      apply Z.le_sub_le_add_r in H5; simpl in H5.
      (* care *)
      clear H15. clear H1 Heqom m.
      apply (Z.le_trans (om + eo + 1) co 127 H13) in H14; clear H13 co;
        apply Z.le_add_le_sub_r in H14; simpl in H14.
      generalize (twos_olen_aux e eo H2 H5 H3); intros.
      rewrite <- Heqt in H.
      lia.
    + (* short exponent *)
      apply Z.lt_le_pred; simpl.
      remember (twos_olen (exp_of_bits (ee + 1) e)) as t.
      replace 1 with (Z.succ 0) in H1 by trivial; apply Z.le_succ_l in H1;
        unfold signif_of_bits; rewrite (Z2Pos.id m H1);
        remember (olen m) as om.
      replace (om + ee + 2) with (om + (ee + 1) + 1) in H13 by lia.
        remember (ee + 1) as eo.
      replace ee with (eo - 1) in * by lia; clear Heqeo.
      apply Z.le_sub_le_add_l in H4; simpl in H4.
      apply Z.le_sub_le_add_r in H5; simpl in H5.
      (* care *)
      clear H15. clear H1 Heqom m.
      apply (Z.le_trans (om + eo + 1) co 127 H13) in H14; clear H13 co;
        apply Z.le_add_le_sub_r in H14; simpl in H14.
      generalize (twos_olen_aux e eo H2 H5 H3); intros.
      rewrite <- Heqt in H.
      lia.
  - (* valid radix *)
    unfold radix_of_bits.
    repeat break_match; auto.
  - (* scaling lower bound *)
    debool;
      replace 0 with (Z.succ (-1)) in H7 by trivial; apply Z.le_succ_l in H7;
      apply H7.
  - (* scaling upper bound *)
    debool;
      apply Zle_lt_succ in H6; apply H6.
Qed.

Lemma valid_long_valid_BER {id co t s bb ff ee eo e m : Z} :
  valid_long id co t s bb ff ee eo e m = true ->
  valid_BER
    (radix_of_bits bb) ff (signif_of_bits m) (exp_of_bits (eo) e) = true.
Proof.
  unfold valid_long. intros H.
  repeat split_andb.
  debool.
  clear H H13 id t.
  clear H11 H12 s.
  unfold valid_BER. apply andb_true_intro; split; apply andb_true_intro; split.
  - (* bounded *)
    clear H7 H8 ff; clear H9 H10 bb.
    unfold bounded.
    break_match; debool.
    + (* long exponent *)
      apply Z.lt_le_pred; simpl.
      remember (twos_olen (exp_of_bits (eo) e)) as t.
      replace 1 with (Z.succ 0) in H1 by trivial; apply Z.le_succ_l in H1;
        unfold signif_of_bits; rewrite (Z2Pos.id m H1);
        remember (olen m) as om.
      generalize (twos_olen_aux e eo H2 H5 H3); intros.
      rewrite <- Heqt in H.
      lia.
    + (* short exponent *)
      apply Z.lt_le_pred; simpl.
      remember (twos_olen (exp_of_bits (eo) e)) as t.
      replace 1 with (Z.succ 0) in H1 by trivial; apply Z.le_succ_l in H1;
        unfold signif_of_bits; rewrite (Z2Pos.id m H1);
        remember (olen m) as om.
      generalize (twos_olen_aux e eo H2 H5 H3); intros.
      rewrite <- Heqt in H.
      lia.
  - (* valid radix *)
    unfold radix_of_bits.
    repeat break_match; auto.
  - (* scaling lower bound *)
    debool; lia.
  - (* scaling upper bound *)
    debool; lia.
Qed.

Lemma valid_BER_valid_radix {b : radix} {f e : Z} {m : positive} :
  valid_BER b f m e = true ->
  valid_radix b = true.
Proof.
  intros H.
  unfold valid_BER in H.
  repeat split_andb.
  apply H2.
Qed.

Theorem BER_bitstring_roundtrip (scaled : bool) (f : BER_float) :
  roundtrip_option
    BER_float BER_bitstring BER_float
    bitstring_of_BER
    BER_of_bitstring
    BER_float_strict_eqb
    f.
Proof.
  unfold roundtrip_option.
  unfold bool_het_inverse'; simpl.
  break_match.
  - (* forward pass successful *)
    intros H; clear H.
    break_match.
    rename b0 into f', Heqo into FP, Heqo0 into BP.
    + (* backward pass successful *)
      destruct f.
      * (* zero *)
        destruct s; inversion FP; subst; inversion BP; subst; trivial.
      * (* infinity *)
        destruct s; inversion FP; subst; inversion BP; subst; trivial.
      * (* nan *)
        inversion FP; subst; inversion BP; subst; trivial.
      * (* finite *)
        simpl in FP.
        unfold bitstring_of_finite_BER in FP.
        destruct (twos_olen e <? 4)%bool;
          break_match; inversion FP; subst; clear FP;
          simpl in BP;
          break_match; inversion BP; subst; clear BP.
        (* TODO: the following two branches should fit in two lines *)
        -- generalize (bits_of_radix_inv b0); intros.
           generalize (bits_of_sign_inv s); intros.
           generalize (bits_of_exp_inv (twos_olen e) e); intros.
           unfold bool_het_inverse in *.
           inversion e0.
           apply valid_BER_valid_radix in H3.
           apply H in H3; clear H.
           assert (H2 : twos_olen e - 1 + 1 = twos_olen e) by lia.
           unfold BER_float_strict_eqb.
           rewrite H3, H0, H2, H1, Z.eqb_refl, Pos.eqb_refl, e0.
           trivial.
        -- generalize (bits_of_radix_inv b0); intros.
           generalize (bits_of_sign_inv s); intros.
           generalize (bits_of_exp_inv (twos_olen e) e); intros.
           unfold bool_het_inverse in *.
           inversion e0.
           apply valid_BER_valid_radix in H3.
           apply H in H3; clear H.
           unfold BER_float_strict_eqb.
           rewrite H3, H0, H1, Z.eqb_refl, Pos.eqb_refl, e0.
           trivial.

    + (* backward pass unsuccessful *)
      exfalso; rename Heqo into FP, Heqo0 into BP.
      unfold BER_of_bitstring in BP.
      repeat break_match; try some_eq_none_inv; clear BP.
      * (* special *)
        unfold bitstring_of_BER in FP.
        break_match; inversion FP; clear FP.
        -- destruct s; inversion H0; subst; inversion Heqo.
        -- destruct s; inversion H0; subst; inversion Heqo.
        -- subst; inversion Heqo.
        -- unfold bitstring_of_finite_BER in H0.
           repeat break_match; inversion H0.
      * (* short *)
        inversion e0.
        apply valid_short_valid_BER in H0.
        rewrite e1 in H0. inversion H0.
      * (* long *)
        inversion e0.
        apply valid_long_valid_BER in H0.
        rewrite e1 in H0. inversion H0.
  - (* forward pass unsuccessful *)
    intros H; inversion H.
Qed.
