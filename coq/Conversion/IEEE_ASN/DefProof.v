Require Import ZArith PArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.IEEEAux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.StructTactics ASN1FP.Aux.Aux
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option ASN1FP.Aux.StrongInduction.

Require Import Lia.

Require Import Flocq.Core.Zaux Flocq.IEEE754.Binary.
Require Import Flocq.Core.Defs.

Open Scope Z.

Section Base2.

  Variable prec emax : Z.
  Variable prec_gt_1 : prec > 1.
  Hypothesis Hmax : (prec < emax)%Z.

  (* only radix = 2 is considered for both formats in this section
   * scaling factor is, therefore, not required in BER
   * TODO: for arbitrary radix/scaling combinations, refer to another section
   *)
  Let r := radix2.
  Let scl := 0.
(* can a given (m,e) pair be represented in IEEE/BER exactly *)
  Let valid_IEEE := bounded prec emax.
  Let valid_BER := valid_BER r scl.

  (* aux: apply variables *)
  Let IEEE_float := binary_float prec emax.
  Let valid_IEEE_sumbool := binary_bounded_sumbool prec emax.
  Let BER_finite_b2 := BER_finite r scl.
  Let valid_BER_sumbool := valid_BER_sumbool r scl.

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

  Section Def.

    (*
     * given a pair (m,e), return (mx, ex) such that
     *   m*2^e = mx*2^ex
     * and
     *   m is odd
     *)
    Definition normalize_BER_finite_nrec (m : positive) (e : Z) : (positive * Z) :=
      let t := N.log2 (((Pos.lxor m (m-1)) + 1) / 2) in
      (Pos.shiftr m t, e + (Z.of_N t)).

    Fixpoint normalize_BER_finite (m : positive) (e : Z) : positive * Z :=
      match m with
      | xO p => normalize_BER_finite p (e + 1)
      | _ => (m, e)
      end.

    (*
     * given all meaningful parts of a BER real, construct it, if possible
     * The content is normalized in accordance with [ 11.3.1 ] if possible
     *)
    Definition make_BER_finite (s : bool) (m : positive) (e : Z)
      : option BER_float :=
      let '(mx, ex) := normalize_BER_finite m e in
      match valid_BER_sumbool mx ex with
      | left V => Some (BER_finite_b2 s mx ex V)
      | right _ => None
      end.
    
    (* TODO: radix, scaling (determine `b` and `ff`) *)
    (*
     * exact conversion from IEEE to BER
     * no rounding is performed: if conversion is impossible without rounding
     * `None` is returned
     *)
    Definition BER_of_IEEE_exact (f : IEEE_float) : option BER_float :=
      match f with
      | B754_zero _ _ s => Some (BER_zero s)
      | B754_infinity _ _ s => Some (BER_infinity s)
      | B754_nan _ _ _ _ _ => Some (BER_nan)
      | B754_finite _ _ s m e _ => make_BER_finite s m e
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

    (*
     * exact conversion from BER to IEEE
     * radix2 with no scaling asssumed: if input does not match, 'None' returned
     * no rounding is performed: if conversion is impossible without rounding
     * `None` is returned
     *)
    Definition IEEE_of_BER_exact (f : BER_float) : option IEEE_float := 
      match f with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_NaN)
      | BER_finite b f s m e _ =>
        if andb (b =? 2) (f =? 0) then
          make_IEEE_finite s m e
        else None
      end.

    (*
     *  given a triple (s,m,e) standing for s*m*2^e,
     *  return a corresponding binary_float,
     *  correctly rounded in accordance with the specified rounding mode
     *)
    Definition round_finite
               (Hmax : prec < emax) (rounding : mode)
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
     *  1) If initial BER encoding has radix /= 2 or scaling factor /= 0
     *     `None` is returned
     *  2) If the ASN encoding is a NaN,
     *     float's NaN payload is set to 1
     *)
    Definition IEEE_of_BER_rounded (Hmax : prec < emax) (rounding : mode) (r : BER_float) : option (IEEE_float) :=
      match r with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_NaN)
      | BER_finite b f s m e x =>
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

    Definition R_of_float (m : positive) (e : Z) :=
      F2R (Float radix2 (Zpos m) e).
      
    Lemma R_of_valid_IEEE_inj {m1 m2 : positive} {e1 e2 : Z} :
      valid_IEEE m1 e1 = true -> valid_IEEE m2 e2 = true ->
      R_of_float m1 e1 = R_of_float m2 e2 ->
      (m1, e1) = (m2,e2).
    Proof.
      intros V1 V2 Req.
      remember (B754_finite prec emax false m1 e1 V1) as f1.
      remember (B754_finite prec emax false m2 e2 V2) as f2.
      assert (fin_f1 : is_finite_strict prec emax f1 = true) by (subst; auto).
      assert (fin_f2 : is_finite_strict prec emax f2 = true) by (subst; auto).
      generalize (B2R_inj prec emax f1 f2 fin_f1 fin_f2); intros.
      unfold B2R in H.
      rewrite Heqf1, Heqf2 in H.
      apply H in Req.
      inversion Req.
      auto.
    Qed.

    Lemma normalize_IEEE_eq (m : positive) (e : Z) :
      R_of_float m e =
      uncurry R_of_float (normalize_IEEE_finite m e).
    Proof.
      unfold R_of_float, normalize_IEEE_finite, uncurry.
      break_let.
      generalize (shl_align_fexp_correct prec emax m e).
      intros H; rewrite Heqp in H; apply proj1 in H.
      apply H.
    Qed.

    Definition Podd (p : positive) : Prop :=
      match p with
      | xO _ => False
      | _ => True
      end.

    Lemma p_lt_2p (p : positive) :
      (p < p~0)%positive.
    Proof. rewrite <- (Pos.add_diag p); lia. Qed.

    Lemma normalize_BER_odd (m : positive) (e : Z) :
      let '(mx, ex) := normalize_BER_finite m e in
      Podd mx.
    Proof.
      generalize e.
      induction m using positive_lt_ind.
      destruct m; try reflexivity.
      simpl.
      assert (H1 : (m < m~0)%positive) by apply p_lt_2p.
      intros.
      apply H with (y := m) (e := e0 + 1) in H1.
      apply H1.
    Qed.

    Lemma normalize_BER_eq (m : positive) :
      forall (e : Z),
      let '(mx, ex) := normalize_BER_finite m e in
      (mx, ex) = (m, e)
      \/
      exists (d : positive),
        m = (mx * 2^d)%positive /\ e = ex - (Zpos d).
    Proof.
      clear Hmax valid_IEEE IEEE_float valid_IEEE_sumbool prec emax prec_gt_1 Hmax.
      clear r scl valid_BER_sumbool BER_finite_b2 valid_BER.

      induction m using positive_lt_ind.
      intros.
      destruct (normalize_BER_finite m e) as (mx,ex) eqn:NB.
      destruct m; try (simpl in NB; tuple_inversion; left; trivial).
      rewrite <- Pos.add_diag.

      simpl in NB.
      assert (H1 : (m < m~0)%positive) by apply p_lt_2p.
      apply H with (y := m) (e := e + 1) in H1.
      rewrite NB in H1.
      destruct H1.
      - tuple_inversion.
        right.
        exists (1%positive). 
        replace (2^1)%positive with 2%positive by trivial.
        lia.
      - right.
        destruct H0 as [d H0].
        exists (d + 1)%positive.
        replace (2^(d + 1))%positive with (2 * (2^d))%positive
          by (rewrite Positive_as_OT.add_1_r, Positive_as_DT.pow_succ_r; trivial).
        lia.
    Qed.

    Lemma normalize_BER_spec (m mx : positive) (e ex : Z) :
      (mx, ex) = normalize_BER_finite m e ->
      Podd mx
      /\
      ((mx, ex) = (m, e)
      \/
      exists (d : positive),
        m = (mx * 2^d)%positive /\ e = ex - (Zpos d)).
    Proof.
      intros NB.
      split.
      - generalize (normalize_BER_odd m e); intros.
        rewrite <- NB in H.
        apply H.
      - generalize (normalize_BER_eq m e); intros.
        rewrite <- NB in H.
        apply H.
    Qed.
    
    Lemma normalize_BER_Req (m : positive) (e : Z) :
      uncurry R_of_float (normalize_BER_finite m e) =
      R_of_float m e.
    Proof.
      unfold R_of_float, uncurry.
      break_let.
      rename p into mx, z into ex, Heqp into H.
      symmetry in H.
      apply normalize_BER_spec in H.
      destruct H as [H0 [H1|H2]].
      -
        tuple_inversion.
        reflexivity.
      -
        destruct H2 as [d [H2 H3]].
        subst.
        rewrite Pos2Z.inj_mul.
        rewrite Pos2Z.inj_pow.
        remember (ex - Z.pos d) as ex'.
        replace (Z.pos d) with (ex - ex') by lia.
        apply (Float_prop.F2R_change_exp radix2).
        lia.
    Qed.

    Let normalize_roundtrip (m : positive) (e : Z) :=
      uncurry normalize_IEEE_finite
              (normalize_BER_finite m e).

    Lemma normalize_roundtrip_eq (m : positive) (e : Z) :
      uncurry R_of_float (normalize_roundtrip m e) =
      R_of_float m e.
    Proof.
      unfold normalize_roundtrip.
      rewrite <- normalize_BER_Req.
      destruct (normalize_BER_finite m e) as (mx,ex) eqn:NB.
      assert (uncurry normalize_IEEE_finite (mx, ex) = normalize_IEEE_finite mx ex)
        by (unfold uncurry; reflexivity).
      rewrite H.
      rewrite <- normalize_IEEE_eq.
      auto.
    Qed.

    Lemma digits2_size (p : positive) :
      Digits.digits2_pos p = Pos.size p.
    Proof.
      induction p; simpl; try rewrite IHp; reflexivity.
    Qed.

    Lemma normalize_roundtrip_valid (m : positive) (e : Z) :
      valid_IEEE m e = true ->
      uncurry valid_IEEE
              (normalize_roundtrip m e) = true.
    Proof.
      (* unfold everything, clean up *)
      unfold normalize_roundtrip.
      destruct (normalize_BER_finite m e) as (mx, ex) eqn:NB.
      destruct (uncurry normalize_IEEE_finite (mx, ex)) as (m', e') eqn:NI.
      unfold uncurry in *.
      unfold normalize_IEEE_finite, valid_IEEE, shl_align_fexp, shl_align, 
        bounded, canonical_mantissa, uncurry, FLT.FLT_exp in *.
      clear r scl valid_IEEE valid_BER IEEE_float valid_IEEE_sumbool
        BER_finite_b2 valid_BER_sumbool normalize_roundtrip.

      (* remove bool *)
      intros H.
      apply andb_prop in H.
      destruct H as [H1 H2];
      apply Zeq_bool_eq in H1.
      apply Zle_bool_imp_le in H2.

      symmetry in NB. apply normalize_BER_spec in NB.
      destruct NB as [H3 H4].

      split_andb_goal; [apply Zeq_bool_true | apply Zle_bool_true];
        rewrite digits2_size in *.
      -
        rewrite Psize_log_inf in *.
        rewrite <- Zlog2_log_inf in *.

        destruct H4.
        tuple_inversion.
        break_match_hyp; try (tuple_inversion; apply H1).
        + rewrite H1 in Heqz. rewrite Z.sub_diag in Heqz. inversion Heqz.
        + destruct H as [d [H0 H5]].
          break_match_hyp.
          * tuple_inversion; lia.
          * tuple_inversion. exfalso. (* Heqz vs goal *) admit.
          * admit.
      -
        destruct H4.
        + tuple_inversion.
          destruct (Z.max (Z.pos (Pos.size m) + e - prec) (3 - emax - prec) - e) eqn:ZMAX;
            try (tuple_inversion; apply H2).
          admit.
        + destruct H as [d [H4 H5]]; subst.
          admit.
    Admitted.

    Theorem arithmetic_roundtrip (m : positive) (e : Z) :
      valid_IEEE m e = true ->
      normalize_roundtrip m e = (m, e).
    Proof.
      intros H.
      copy_apply normalize_roundtrip_valid H.
      unfold normalize_roundtrip, uncurry in *.
      destruct normalize_BER_finite as (mx,ex) eqn:NB.
      destruct normalize_IEEE_finite as (m',e') eqn:NI.
      apply R_of_valid_IEEE_inj.
      apply H0.
      apply H.
      assert (R_of_float m' e' = uncurry R_of_float (normalize_roundtrip m e)) by
        (unfold uncurry, normalize_roundtrip; rewrite NB, NI; reflexivity).
      rewrite H1.
      apply normalize_roundtrip_eq.
    Qed.

    Ltac inv_make_BER_finite :=
      match goal with
      | [ H : make_BER_finite _ _ _ = Some _ |- _ ] =>
        unfold make_BER_finite in H;
        destruct normalize_BER_finite;
        destruct valid_BER_sumbool;
        inversion H
    end.

    Ltac bcompare_nrefl :=
      match goal with
      | [ H: Bcompare _ _ _ _ = _ |- _] =>
        assert (H1 := H); rewrite -> Bcompare_swap in H1; rewrite -> H in H1; inversion H1
      end.
    
    Theorem main_roundtrip (scaled : bool) (f : IEEE_float):
      roundtrip_option
        IEEE_float BER_float IEEE_float
        (BER_of_IEEE_exact)
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
            copy_apply (arithmetic_roundtrip m e) e0.
            unfold normalize_roundtrip in H.
            rewrite -> NB in H.
            simpl in H.
            rewrite -> NI in H.
            inversion H; subst.
            unfold float_eqb_nan_t, Bcompare.
            repeat break_match; (repeat try some_inv);
              try compare_nrefl; try reflexivity.
    
        + (* backward pass unsuccessful *)
          destruct f; simpl in Heqo; inversion Heqo; subst; inversion Heqo0.
          clear H0 H1; exfalso.
          unfold make_BER_finite in Heqo.
          destruct normalize_BER_finite eqn:NB, valid_BER_sumbool;
            inversion Heqo; clear Heqo.
          subst.
          unfold BER_finite_b2 in Heqo0.
          simpl in Heqo0.
          unfold make_IEEE_finite in Heqo0.
          destruct normalize_IEEE_finite eqn:NI.
          destruct valid_IEEE_sumbool; inversion Heqo0; clear Heqo0.
          copy_apply (arithmetic_roundtrip m e) e0.
          unfold normalize_roundtrip in H.
          rewrite -> NB in H.
          simpl in H.
          rewrite -> NI in H.
          inversion H; subst.
          rewrite e0 in e2; inversion e2.
      - (* forward pass unsuccessful *)
        inversion FPT.
    Qed.
    
  End Proof.

End Base2.