Require Import ZArith PArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.IEEEAux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.StructTactics ASN1FP.Aux.Aux
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option.

Require Import Flocq.Core.Zaux Flocq.IEEE754.Binary.

Section Conversion.

  Variable prec emax : Z.
  Variable prec_gt_1 : prec > 1.

  (* 1 can always be the payload of a NaN *)
  Lemma def_NaN :
    nan_pl prec 1 = true.
  Proof.
    unfold nan_pl. simpl.
    apply Z.ltb_lt, Z.gt_lt, prec_gt_1.
  Qed.

    Lemma prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec.
    Proof.
      unfold Flocq.Core.FLX.Prec_gt_0.
      apply (Z.lt_trans 0 1 prec).
      - (* 1 < 0 *)
        reflexivity.
      - (* 1 < prec *)
        apply Z.gt_lt.
        apply prec_gt_1.
    Qed.

  Definition IEEE_float := binary_float prec emax.
  Definition valid_IEEE := bounded prec emax.
  Definition valid_IEEE_sumbool := binary_bounded_sumbool prec emax.

  Section Def.

    (* TODO: recursive definition *)
    (*
     * given a pair (m,e), return (mx, ex) such that
     *   m*2^e = mx*2^ex
     * and
     *   m is odd
     *)
    Definition normalize_BER_finite (m : positive) (e : Z) : (positive * Z) :=
      let t := N.log2 (((Pos.lxor m (m-1)) + 1) / 2) in
      (Pos.shiftr m t, e + (Z.of_N t)).

    (* TODO: add missing normalization parts *)
    (*
     * given all meaningful parts of a BER real, construct it, if possible
     * The content is normalized in accordance with [ 11.3.1 ] if possible
     *)
    Definition make_BER_finite (s : bool) (b : radix) (ff : Z) (m : positive) (e : Z)
      : option BER_float :=
      let '(mx, ex) := normalize_BER_finite m e in
      match valid_BER_sumbool b ff mx ex with
      | left V => Some (BER_finite s b ff mx ex V)
      | right _ => None
      end.
    
    (* TODO: radix, scaling (determine `b` and `ff`) *)
    (*
     * exact conversion from IEEE to BER
     * no rounding is performed: if conversion is impossible without rounding
     * `None` is returned
     *)
    Definition BER_of_IEEE_exact (scaled : bool) (f : IEEE_float) : option BER_float :=
      let b := radix2 in
      let ff := 0%Z in
      match f with
      | B754_zero _ _ s => Some (BER_zero s)
      | B754_infinity _ _ s => Some (BER_infinity s)
      | B754_nan _ _ _ _ _ => Some (BER_nan)
      | B754_finite _ _ s m e _ => make_BER_finite s b ff m e
      end.

    (*
     * turn any pair (m,e) into a pair (mx,ex), representable in
     * IEEE 745 if possible. No rounding is performed,
     * (m,e) remains unchanged if normalization is impossible without rounding
     *)
    Definition normalize_IEEE_finite : positive -> Z -> (positive * Z) :=
      shl_align_fexp prec emax.

    (* given all meaningful parts of an IEEE float, construct it, if possible *)
    Definition make_IEEE_finite (s : bool) (m : positive) (e : Z) : option IEEE_float :=
      let '(mx, ex) := normalize_IEEE_finite m e in
      match (valid_IEEE_sumbool mx ex) with
      | left V => Some (B754_finite _ _ s mx ex V)
      | right _ => None
      end.

    (* TODO: radix, scaling (remove `if`, handle conversion properly) *)
    (*
     * exact conversion from BER to IEEE
     * no rounding is performed: if conversion is impossible without rounding
     * `None` is returned
     *)
    Definition IEEE_of_BER_exact (f : BER_float) : option IEEE_float := 
      match f with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_NaN)
      | BER_finite s b f m e _ =>
        if andb (b =? 2) (f =? 0) then
          make_IEEE_finite s m e
        else None
      end.

    (*
     *  given a triple (s,m,e) standing for s*m*2^e,
     *  return a corresponding binary_float,
     *  correctly rounded in accordance with the specified rounding mode
     *)
    Definition round_finite (Hmax : prec < emax) (rounding : mode)
               (s : bool) (m : positive) (e : Z) : IEEE_float :=
      binary_normalize
        prec emax prec_gt_0 Hmax
        rounding
        (cond_Zopp s (Zpos m)) e s.

    (*
     *  for any ASN.1 BER-encoded real number s*m*(b^e)
     *  return the number's representation in the target IEEE format
     *  rounded in accordnace with the provided rounding mode if necessary
     *
     *  NOTE:
     *  2) If initial BER encoding has radix /= 2,
     *     `None` is returned
     *  3) If the ASN encoding is a NaN,
     *     float's NaN payload is set to 1
     *)
    (* TODO: scaling *)
    (* TODO: radix *)
    Definition IEEE_of_BER_rounded (Hmax : prec < emax) (rounding : mode) (r : BER_float) : option (IEEE_float) :=
      match r with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_NaN)
      | BER_finite s b f m e x =>
        if andb (b =? 2) (f =? 0)
        then Some (round_finite Hmax rounding s m e)
        else None
      end.
    
    (*
     *  given a binary_float and a rounding mode
     *  convert it to target format, rounding if necessary
     *
     *  NaN payload is set to 1 uncoditionally
     *)
    Definition IEEE_of_IEEE_round_reset_nan (Hmax : prec < emax) (rounding : mode) (f : IEEE_float) : IEEE_float :=
      match f with
      | B754_nan _ _ _ _ _ => B754_nan _ _ false 1 def_NaN
      | B754_infinity _ _ s => B754_infinity _ _ s
      | B754_zero _ _ s => B754_zero _ _ s
      | B754_finite _ _ s m e _ => round_finite Hmax rounding s m e
      end.

  End Def.

  Section Proof.
    
    Ltac bcompare_nrefl :=
      match goal with
      | [ H: Bcompare _ _ _ _ = _ |- _] =>
        assert (H1 := H); rewrite -> Bcompare_swap in H1; rewrite -> H in H1; inversion H1
      end.

    Lemma arithmetic_roundtrip {m : positive} {e : Z} (V : valid_IEEE m e = true) :
      uncurry normalize_IEEE_finite (normalize_BER_finite m e) = (m, e).
    Admitted.
    
    Definition supported_IEEE (f : IEEE_float) : bool :=
      match f with
      | B754_finite _ _ _ m e _ => uncurry (valid_BER radix2 0) (normalize_BER_finite m e)
      | _ => true
      end.
      
    Lemma forward_pass_guarantee (scaled : bool) (f : IEEE_float) :
      supported_IEEE f = true <->
      is_Some_b (BER_of_IEEE_exact scaled f) = true.
    Proof.
      split.
      - (* supported -> passes *)
        unfold supported_IEEE, is_Some_b, BER_of_IEEE_exact, make_BER_finite.
        intros.
        repeat break_match; try reflexivity; inversion H; inversion Heqo.
        rewrite -> e1 in H1.
        inversion H1.
      - (* passes -> supported *)
        destruct f eqn:F; try reflexivity.
        unfold BER_of_IEEE_exact, make_BER_finite, supported_IEEE.
        repeat break_match.
        + (* valid_BER *)
          simpl; intros G; clear G.
          apply e1.
        + (* not valid_BER *)
          intros H; inversion H.
    Qed.

    Let l1 {A B : Type } (f : A -> option B) : (option A -> option B) :=
      fun x : option A =>
        match x with
        | Some a => f a
        | None => None
        end.
    
    Lemma backward_pass_guarantee (scaled : bool) (f : IEEE_float) :
      supported_IEEE f = true ->
      is_Some_b ((l1 IEEE_of_BER_exact) (BER_of_IEEE_exact scaled f)) = true.
    Proof.
      unfold is_Some_b, l1.
      repeat break_match; try reflexivity.
      - (* yes forward, no backward *)
        exfalso.
        clear l1.
        destruct f; simpl in Heqo0; inversion Heqo0.
        + rewrite <- H0 in Heqo; simpl in Heqo; inversion Heqo.
        + rewrite <- H0 in Heqo; simpl in Heqo; inversion Heqo.
        + rewrite <- H0 in Heqo; simpl in Heqo; inversion Heqo.
        + clear H0.
          unfold make_BER_finite in Heqo0.
          destruct normalize_BER_finite eqn:NB.
          destruct valid_BER_sumbool; inversion Heqo0; clear Heqo0.
          rewrite <- H0 in Heqo.
          simpl in Heqo.
          unfold make_IEEE_finite in Heqo.
          destruct normalize_IEEE_finite eqn:NI.
          destruct valid_IEEE_sumbool; inversion Heqo; clear Heqo.
          generalize dependent (arithmetic_roundtrip e0); intros.
          rewrite -> NB in H.
          simpl in H.
          rewrite -> NI in H.
          inversion H; subst.
          rewrite e0 in e2.
          inversion e2.
      - (* no forward *)
        intros.
        exfalso; generalize dependent (forward_pass_guarantee scaled f); intros.
        apply H0 in H; clear H0.
        rewrite -> Heqo0 in H.
        inversion H.
    Qed.

    Ltac inv_make_BER_finite :=
      match goal with
      | [ H : make_BER_finite _ _ _ _ _ = Some _ |- _ ] =>
        unfold make_BER_finite in H;
        destruct normalize_BER_finite;
        destruct valid_BER_sumbool;
        inversion H
    end.

    Theorem main_roundtrip (scaled : bool) (f : IEEE_float):
      roundtrip_option
        IEEE_float BER_float IEEE_float
        (BER_of_IEEE_exact scaled)
        IEEE_of_BER_exact
        (float_eqb_nan_t)
        f.
    Proof.
      intros FPT.
      unfold bool_het_inverse'; simpl.
      break_match.
      - (* forward pass successful *)
        clear FPT.
        break_match.
        + (* backward pass successful *)
          destruct f; destruct b; simpl in *; repeat try some_inv; try auto.
          (* structural errors *)
          * unfold float_eqb_nan_t, Bcompare.
            repeat break_match; (repeat try some_inv);
              try compare_nrefl; try reflexivity.
          * inv_make_BER_finite.
          * inv_make_BER_finite.
          * inv_make_BER_finite.
    
          * (* arithmetic_roundtrip comes in play *)
             destruct ((b =? 2) && (f =? 0))%bool; inversion Heqo0; clear H0.
    
            (* simplify forward conversions *)
            unfold make_BER_finite in *.
            destruct normalize_BER_finite eqn:NB.
            destruct valid_BER_sumbool; inversion Heqo.
            clear Heqo; subst.
            
            (* simplify backward conversions *)
            unfold make_IEEE_finite in *.
            destruct normalize_IEEE_finite eqn:NI.
            destruct valid_IEEE_sumbool; inversion Heqo0.
            clear Heqo0; subst.
    
            (* apply arithmetic roundtrip *)
            generalize dependent (arithmetic_roundtrip e0); intros.
            rewrite -> NB in H.
            simpl in H.
            rewrite -> NI in H.
            inversion H; clear H; subst.
            unfold float_eqb_nan_t, Bcompare.
            repeat break_match; (repeat try some_inv);
              try compare_nrefl; try reflexivity.
    
        + (* backward pass unsuccessful *)
          exfalso.
          generalize dependent (backward_pass_guarantee scaled f); intros.
          rewrite -> Heqo in H; simpl in H.
          rewrite -> Heqo0 in H.
          assert (H1 : supported_IEEE f = true).
          {
            rewrite -> (forward_pass_guarantee scaled f), Heqo.
            reflexivity.
          }
          apply H in H1.
          inversion H1.
      - (* forward pass unsuccessful *)
        inversion FPT.
    Qed.

  End Proof.

End Conversion.