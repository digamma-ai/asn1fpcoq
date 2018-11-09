Require Import ZArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.IEEEAux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Option ASN1FP.Aux.StructTactics ASN1FP.Aux.Tactics
        ASN1FP.Conversion.IEEE_ASN.Def.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux.

Section Conversions.

  Variable prec emax : Z.
  Variable prec_gt_1: Prec_gt_1 prec.

  Let float := binary_float prec emax.
  Let binary_bounded_sumbool := binary_bounded_sumbool prec emax.

  Section Exact.

    (*
     *  roundtrip statement for IEEE->BER->IEEE conversion with no rounding
     *  (see `roundtrip`)
     *  
     *  Two IEEE floats are equivalent here
     *  if and only if
     *      they are strictly equal
     *    or
     *      they both encode a NaN
     *      (in which case NaN payload is not taken into account)
     *)
    Theorem IEEE_BER_roundtrip_exact (scaled : bool) (f : float):
      roundtrip_option
        float BER_float float
        (IEEE_to_BER_exact prec emax scaled)
        (BER_to_IEEE_exact prec emax prec_gt_1)
        (float_eqb_nan_t)
        f.
    Proof.
      intros FPT.

      unfold bool_het_inverse', float_eqb_nan_t. simpl.
      unfold IEEE_to_BER_exact, BER_to_IEEE_exact, Bcompare in *.

      repeat break_match; try some_eq_none_inv; (repeat try some_inv); subst;
        try reflexivity; try true_eq_false_inv;
          try compare_nrefl; try check_contradiction.

      (* if IEEE -> BER returns radix /= 2 *)
      inversion Heqb1.

      (* if IEEE -> BER returns None *)
      inversion FPT.
    Qed.

    (* Indicator function on the supported subset of floats *)
    (* TODO: scaling *)
    (* TODO: radix *)
    Definition is_exact_convertible_IEEE (f : float) : bool :=
      match f with
      | B754_finite _ _ _ m e _ => valid_BER radix2 0 m e
      | _ => true
      end.

    (*
     *  Guarantees that for all supported float values
     *  (those given by `is_exact_convertible_IEEE`)
     *  forward pass does not generate an error
     *)
    Theorem IEEE_BER_pass_guarantee :
      forall (f : float),
        is_exact_convertible_IEEE f = true ->
        is_Some_b (IEEE_to_BER_exact prec emax false f) = true.
    Proof.
      intros f.
      unfold is_exact_convertible_IEEE.
      unfold IEEE_to_BER_exact.
      case f.
      (* B754_zero *)
      reflexivity.
      (* B754_infinity *)
      reflexivity.
      (* B754_nan *)
      reflexivity.
      (* B754_finite *)
      intros s m e B.
      unfold IEEE_to_BER_exact.
      case valid_BER_sumbool.
      (* good_real = true *)
      intros GR1 GR2.
      reflexivity.
      (* good_real = false *)
      intros H1 H2.
      rewrite -> H1 in H2.
      inversion H2.
    Qed.

  End Exact.

  Section Rounded.

    Variable target_prec target_emax : Z.
    Variable target_prec_gt_1 : Prec_gt_1 target_prec.
    Variable target_Hmax : (target_prec < target_emax)%Z.

    Let target_float := binary_float target_prec target_emax.

    (* 1 (the number) can always be the payload of a NaN *)
    Lemma def_target_NaN :
      nan_pl target_prec 1 = true.
    Proof.
      unfold nan_pl. simpl.
      apply Z.ltb_lt, Z.gt_lt, target_prec_gt_1.
    Qed.

    (*
     *  given a triplet (s,m,e) standing for s*m*2^e,
     *  return a corresponding binary_float object in target form,
     *  correctly rounded in accordance with the specified rounding mode
     *)
    Definition round_finite (rounding : mode) (s : bool) (m : positive) (e : Z) : target_float :=
      binary_normalize
        target_prec target_emax (target_prec_gt_0 target_prec target_prec_gt_1) target_Hmax
        rounding
        (cond_Zopp s (Zpos m)) e s.


    (*
     *  for two binary_float`s in starting and target formats,
     *  check if the second is the result of
     *  converting (rounded accordingly) the first to target format
     *)
    Definition correctly_rounded_nan_t (rounding : mode) (f : float) (cf : target_float) :=
      float_eqb_nan_t
        (IEEE_to_IEEE_round_reset_nan prec emax target_prec target_emax target_prec_gt_1 target_Hmax rounding f)
        cf.

    (*
     *  roundtrip statement for IEEE->BER->IEEE conversion with rounding
     *  (see `roundtrip`)
     *  
     *  Rounding only happens during the backwards conversion (BER->IEEE)
     *  Forward pass only attempts to represent the IEEE float in BER exactly
     *  
     *  Resulting float is equivalent to the starting one
     *  if and only if
     *      it is encoding a  real number strictly equal to that of the starting one
     *    or
     *      it is a result of a correct rounding as specified in the IEEE-754 standard
     *      (see IEEE Std 754-2008 clause 5.4.2)
     *    or
     *      both floats are NaN
     *      (in which case payloads are not taken into accout)
     *)
    Theorem IEEE_BER_roundtrip_rounded (rounding : mode) (scaled : bool) (f : float) :
      roundtrip_option
        float BER_float target_float
        (IEEE_to_BER_exact prec emax scaled)
        (BER_to_IEEE_rounded target_prec target_emax target_prec_gt_1 target_Hmax rounding)
        (correctly_rounded_nan_t rounding)
        f.
    Proof.
      unfold roundtrip_option.
      intros I2BS.
      unfold bool_het_inverse', float_eqb_nan_t. simpl.
      unfold IEEE_to_BER_exact, BER_to_IEEE_rounded, correctly_rounded_nan_t,
      float_eqb_nan_t, IEEE_to_IEEE_round_reset_nan in *.
      repeat break_match; try some_eq_none_inv; (repeat try some_inv); subst; try reflexivity;
        try compare_nrefl; try bcompare_nrefl.

      (* if IEEE -> BER returns radix /= 2 *)
      inversion Heqb1.
      (* if IEEE -> BER returns None *)
      inversion I2BS.
    Qed.

  End Rounded.

End Conversions.
