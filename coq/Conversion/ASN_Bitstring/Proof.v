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

 Lemma valid_short_valid_BER {id co t s bb ff ee e m : Z} :
   valid_short id co t s bb ff ee e m = true ->
   valid_BER
    (radix_of_bits bb) ff (signif_of_bits m) (exp_of_bits (ee + 1) e) = true.
 Proof.
   unfold valid_short. intros H.
   unfold valid_BER. apply andb_true_intro. split.
   unfold correct_short_co in H.
   repeat split_andb; rewrite Z.ltb_lt in *; rewrite Z.eqb_eq in *.
   clear H0 H6 H7 H8 H9 H10 H11 H12.
   apply Z.lt_le_pred in H.

   (*
   apply (Z.le_trans (eeo + olen m) (co - 1) 126) in H; try lia.
   apply (Z.le_trans (olen e) (ee+2-1) 3) in H3; try lia.
   *)
   (* - (* bounded *) *)
   (*   unfold bounded. *)
   (*   break_match; rewrite Z.ltb_lt in *. *)
   (*   + (* long *) *)
   (*     contradict Heqb. *)
   (*     rewrite not_Zlt_Zle. *)
   (*     unfold exp_of_bits. *)
   (*     admit. *)
   (*   + (* short *) *)
   (*     unfold signif_of_bits; rewrite Z2Pos.id. *)
   (*     rewrite Z.ltb_ge in Heqb. *)
 Admitted.

 Lemma valid_long_valid_BER {id co t s bb ff ee eo e m : Z} :
   valid_long id co t s bb ff ee eo e m = true ->
   valid_BER
     (radix_of_bits bb) ff (signif_of_bits m) (exp_of_bits (eo) e) = true.
 Admitted.

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
