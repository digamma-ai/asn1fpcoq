Require Import ZArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.IEEEAux
               ASN1FP.Aux.Roundtrip ASN1FP.Aux.Option ASN1FP.Aux.StructTactics ASN1FP.Aux.Tactics.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.Core.FLX.

Definition Prec_gt_1 (prec : Z) := Z.gt prec 1.

Section Conversions.

  Variable prec emax: Z.
  Variable prec_gt_1: Prec_gt_1 prec.

  Let float := binary_float prec emax.
  Let binary_bounded_sumbool := binary_bounded_sumbool prec emax.

  Section Exact.

    Lemma prec_gt_0 : Prec_gt_0 prec.
    Proof.
      unfold Prec_gt_0.
      apply (Z.lt_trans 0 1 prec).
      - (* 1 < 0 *)
        reflexivity.
      - (* 1 < prec *)
        apply Z.gt_lt.
        apply prec_gt_1.
    Qed.

    (* 1 (the number) can always be the payload of a NaN *)
    Lemma def_NaN :
      nan_pl prec 1 = true.
    Proof.
      unfold nan_pl. simpl.
      apply Z.ltb_lt, Z.gt_lt, prec_gt_1.
    Qed.

    (*
     *  for any float s*m*(2^e)
     *  return its ASN.1 BER representation if possible
     *  
     *  NOTE:
     *  1) ASN.1 BER representation is set to have radix = 2
     *     (directly resembling the IEEE-754 radix)
     *  2) Only direct conversion is attempted
     *     (i.e. (s,m,e) -> (s,m,e)
     *     not (s,m,e) -> (s,m*2,e-1))
     *  3) If direct conversion is impossible,
     *     `None` is returned
     *  4) After the conversion, IEEE-754 NaN payload is lost,
     *     as it is not supported by the ASN.1 standard
     *)
    (* TODO: scaling *)
    Let mptd (m : positive) : N :=
      N.log2 (((Pos.lxor m (m-1)) + 1) / 2).

    Definition normalize (m : positive) (e : Z) : positive * Z :=
      let t := mptd m in
      (Pos.shiftr m t, e + (Z.of_N t)).

    (* Fixpoint normalize (m : positive) (e : Z) : positive * Z := *)
    (*   if ((Zpos m) mod 2) =? 0 *)
    (*   then normalize (Pos.shiftr m 1) (e + 1) *)
    (*   else (m,e). *)
    
    
    Definition IEEE_to_BER_exact (scaled : bool) (f : float) : option BER_float :=
      let ff := 0%Z in
      match f with
      | B754_zero _ _ s => Some (BER_zero s)
      | B754_infinity _ _ s => Some (BER_infinity s)
      | B754_nan _ _ _ _ _ => Some (BER_nan)
      | B754_finite _ _ s m e _ =>
        let '(mx, ex) := normalize m e in
        match valid_BER_sumbool radix2 ff mx ex with
        | left G => Some (BER_finite s radix2 ff mx ex G)
        | right _ => None
        end
      end.

    (*
     *  for any ASN.1 BER-encoded real number s*m*(b^e)
     *  return the number's representation in the target IEEE format if possible
     *  
     *  NOTE:
     *  1) Only direct conversion is attempted
     *     (i.e. (s,m,e) -> (s,m,e)
     *     not  (s,m,e) -> (s,m*2,e-1))
     *  2) If direct conversion is impossible or
     *     initial BER encoding has radix /= 2,
     *     `None` is returned
     *  3) If the BER encoding is a NaN,
     *     float's NaN payload is set to 1
     *)
    (* TODO: radix *)
    (* TODO: scaling *)
    Let shl_align_fexp := shl_align_fexp prec emax.

    Definition BER_to_IEEE_exact (r : BER_float) : option float :=
      match r with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_NaN)
      | BER_finite s b f m e x =>
        if andb (b =? 2) (f =? 0)
        then
          let
            '(mx,ex) := shl_align_fexp m e in
          match binary_bounded_sumbool mx ex with
             | left B => Some (B754_finite _ _ s mx ex B)
             | right _ => None
             end
        else None
      end.

  End Exact.

  Section Rounded.

    Variable target_prec target_emax : Z.
    Variable target_prec_gt_1 : Prec_gt_1 target_prec.
    Variable target_Hmax : (target_prec < target_emax)%Z.

    Let target_float := binary_float target_prec target_emax.

    Lemma target_prec_gt_0 : Prec_gt_0 target_prec.
    Proof.
      unfold Prec_gt_0.
      apply (Z.lt_trans 0 1 target_prec).
      - (* 1 < 0 *)
        reflexivity.
      - (* 1 < prec *)
        apply Z.gt_lt.
        apply target_prec_gt_1.
    Qed.

    (* 1 (the number) can always be the payload of a NaN *)
    Lemma def_target_NaN :
      nan_pl target_prec 1 = true.
    Proof.
      unfold nan_pl. simpl.
      apply Z.ltb_lt, Z.gt_lt, target_prec_gt_1.
    Qed.

    (*
     *  given a triple (s,m,e) standing for s*m*2^e,
     *  return a corresponding binary_float object in target form,
     *  correctly rounded in accordance with the specified rounding mode
     *)
    Definition round_finite (rounding : mode) (s : bool) (m : positive) (e : Z) : target_float :=
      binary_normalize
        target_prec target_emax target_prec_gt_0 target_Hmax
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
    Definition BER_to_IEEE_rounded (rounding : mode) (r : BER_float) : option (target_float) :=
      match r with
      | BER_zero s => Some (B754_zero _ _ s)
      | BER_infinity s => Some (B754_infinity _ _ s)
      | BER_nan => Some (B754_nan _ _ false 1 def_target_NaN)
      | BER_finite s b f m e x =>
        if andb (b =? 2) (f =? 0)
        then Some (round_finite rounding s m e)
        else None
      end.

    (*
     *  given a binary_float and a rounding mode
     *  convert it to target format, rounding if necessary
     *  
     *  NaN payload is set to 1 uncoditionally
     *)
    Definition IEEE_to_IEEE_round_reset_nan (rounding : mode) (f : float) : target_float :=
      match f with
      | B754_nan _ _ _ _ _ => B754_nan _ _ false 1 def_target_NaN
      | B754_infinity _ _ s => B754_infinity _ _ s
      | B754_zero _ _ s => B754_zero _ _ s
      | B754_finite _ _ s m e _ => round_finite rounding s m e
      end.

  End Rounded.

End Conversions.
