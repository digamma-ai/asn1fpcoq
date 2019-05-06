Require Import ZArith Lia.
Require Import ASN1FP.Types.ASN ASN1FP.Types.Bitstring
        ASN1FP.Aux.Bits ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics ASN1FP.Aux.Roundtrip.
Require Import Flocq.Core.Zaux.

Open Scope Z.

Section Definitions.

  Section Atomic.
  
    (*
     * functions converting individual meaningful parts of a BER-encoded real
     * to their corresponding binary strings
     *)
  
    (* [ 8.5.7.2 ] *)
    Definition bits_of_radix (b : radix) : Z :=
      if Z.eqb b 2 then 0
      else if Z.eqb b 4 then 1
          else if Z.eqb b 8 then 2
                else if Z.eqb b 16 then 3
                    else 0.
  
    Definition radix_of_bits (b : Z) : radix :=
      if Z.eqb b 0 then radix2
      else if Z.eqb b 1 then radix4
          else if Z.eqb b 2 then radix8
                else if Z.eqb b 3 then radix16
                    else radix2.
  
    (* [ 8.5.7.1 ] *)
    Definition bits_of_sign (s : bool) : Z :=
      if s then 1 else 0.
  
    Definition sign_of_bits (s : Z) : bool :=
      if (Z.eqb s 1) then true else false.
  
    (* [ 8.5.7.5 ] *)
    Definition bits_of_signif (m : positive) : Z :=
      Zpos m.
  
    Definition signif_of_bits (m : Z) : positive :=
      Z.to_pos m.
  
    (* [ 8.5.7.4 ] *)
    Definition bits_of_exp (e_olen e : Z) : Z :=
      twos_comp_extended (8 * e_olen) e.
  
    Definition exp_of_bits (e_olen e : Z) : Z :=
      twos_comp_extended (8 * e_olen) e.
  
  End Atomic.
  
  Definition bitstring_of_finite_BER
              (b : radix) (f : Z) (s : bool) (m : positive) (e : Z) : option BER_bitstring :=
    let m := bits_of_signif m in
    let s := bits_of_sign s in
    let bb := bits_of_radix b in
    let e_olen := twos_olen e in let e := bits_of_exp e_olen e in
      if Z.ltb (e_olen) 4
      then
        match (valid_short_sumbool real_id_b (e_olen + olen m + 1) binary_bit s bb f (e_olen - 1) e m) with
        | right _ => None
        | left V => Some (short real_id_b (e_olen + olen m + 1) binary_bit s bb f (e_olen - 1) e m V)
        end
      else
        match (valid_long_sumbool real_id_b (e_olen + olen m + 2) binary_bit s bb f 3 e_olen e m) with
            | right _ => None
            | left V => Some (long real_id_b (e_olen + olen m + 2) binary_bit s bb f 3 e_olen e m V)
        end.
  
  Definition bitstring_of_BER (f : BER_float) : option BER_bitstring :=
    match f with
    | BER_zero s => Some (if s then special nzero else special pzero)
    | BER_infinity s => Some (if s then special ninf else special pinf)
    | BER_nan => Some (special nan)
    | BER_finite s b ff m e _ => bitstring_of_finite_BER s b ff m e
    end.
  
  Definition BER_of_bitstring (b : BER_bitstring) : option BER_float :=
    match b with
    | special val =>
      match val with
      | pzero => Some (BER_zero false)
      | nzero => Some (BER_zero true)
      | pinf => Some (BER_infinity false)
      | ninf => Some (BER_infinity true)
      | nan => Some (BER_nan)
      end
    | short id co t s bb ff ee e m _ =>
      let s := (sign_of_bits s) in
      let b := (radix_of_bits bb) in
      let m := (signif_of_bits m) in
      let e := (exp_of_bits (ee + 1) e) in
      match valid_BER_sumbool b ff m e with
      | right _ => None
      | left V => Some (BER_finite b ff s m e V)
      end
    | long id co t s bb ff ee eo e m _ =>
      let s := (sign_of_bits s) in
      let b := (radix_of_bits bb) in
      let m := (signif_of_bits m) in
      let e := (exp_of_bits (eo) e) in
      match valid_BER_sumbool b ff m e with
      | right _ => None
      | left V => Some (BER_finite b ff s m e V)
      end
    end.
  
End Definitions.



Section Correctness.

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
        * rewrite (valid_short_valid_BER e0) in e1; inversion e1.
        * rewrite (valid_long_valid_BER e0) in e1; inversion e1.
    - (* forward pass unsuccessful *)
      intros H; inversion H.
  Qed.

End Correctness.
