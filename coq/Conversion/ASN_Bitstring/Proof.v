Require Import ZArith.
Require Import Lia.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.StructTactics ASN1FP.Aux.Bits ASN1FP.Aux.Tactics
        ASN1FP.Conversion.ASN_Bitstring.Def.
Require Import Flocq.Core.Zaux.

Open Scope Z.

Section Atomic.

Lemma radix2bits_inv (b : radix) :
  valid_radix b = true ->
  bool_het_inverse
    radix Z radix
    radix2bits
    bits2radix 
    Z.eqb
    b.
Proof.
  intros H.
  unfold bool_het_inverse, Basics.compose, bits2radix, radix2bits.
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

Lemma sign2bits_inv (s : bool) :
  bool_het_inverse
    bool Z bool
    sign2bits
    bits2sign
    Bool.eqb
    s.
Proof.
  unfold bool_het_inverse, bits2sign, sign2bits.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.

 Lemma signif2bits_inv (m : positive) :
  bool_het_inverse
	positive Z positive
	signif2bits
	bits2signif
	Pos.eqb
	m.
Proof.
  unfold bool_het_inverse, bits2signif, signif2bits.
  simpl. apply Pos.eqb_refl.
Qed.

Lemma exp2bits_inv (e_olen e  : Z) :
  bool_het_inverse
    Z Z Z
    (exp2bits e_olen)
    (bits2exp e_olen)
    Z.eqb
    e.
Proof.
  apply twos_comp_extended_roundtrip.
Qed.

End Atomic.

(******************************************************************************)
(*  Lemma Zlt_Zle (a b : Z) :                                                 *)
(*    a < b <-> a <= b - 1.                                                   *)
(*  Proof. lia. Qed.                                                          *)
(*                                                                            *)
(*  Lemma not_Zlt_Zle (a b : Z) :                                             *)
(*    ~ a < b <-> b <= a.                                                     *)
(*  Proof. lia. Qed.                                                          *)
(*                                                                            *)
(*                                                                            *)
(*  Lemma valid_short_valid_BER {id co t s bb ff ee e m : Z} :                *)
(*    valid_short id co t s bb ff ee e m = true ->                            *)
(*    valid_BER (bits2signif m) (bits2exp (ee + 1) e) (bits2radix bb) = true. *)
(*  Proof.                                                                    *)
(*    unfold valid_short. intros H.                                           *)
(*    unfold valid_BER. apply andb_true_intro. split.                         *)
(*    unfold correct_short_co in H.                                           *)
(*    repeat split_andb; rewrite Z.ltb_lt in *; rewrite Z.eqb_eq in *.        *)
(*    remember (ee+1) as eeo eqn:EEO.                                         *)
(*    clear H0 H6 H7 H8 H9 H10 H11 H12.                                       *)
(*    try rewrite Zlt_Zle in *.                                               *)
(*    apply (Z.le_trans (eeo + olen m) (co - 1) 126) in H; try lia.           *)
(*    apply (Z.le_trans (olen e) (ee+2-1) 3) in H3; try lia.                  *)
(*    (* - (* bounded *) *)                                                   *)
(*    (*   unfold bounded. *)                                                 *)
(*    (*   break_match; rewrite Z.ltb_lt in *. *)                             *)
(*    (*   + (* long *) *)                                                    *)
(*    (*     contradict Heqb. *)                                              *)
(*    (*     rewrite not_Zlt_Zle. *)                                          *)
(*    (*     unfold bits2exp. *)                                              *)
(*    (*     admit. *)                                                        *)
(*    (*   + (* short *) *)                                                   *)
(*    (*     unfold bits2signif; rewrite Z2Pos.id. *)                         *)
(*    (*     rewrite Z.ltb_ge in Heqb. *)                                     *)
(*  Admitted.                                                                 *)
(*                                                                            *)
(*  Lemma valid_long_valid_BER {id co t s bb ff ee eo e m : Z} :              *)
(*    valid_long id co t s bb ff ee eo e m = true ->                          *)
(*    valid_BER (bits2signif m) (bits2exp (eo) e) (bits2radix bb) = true.     *)
(*  Admitted.                                                                 *)
(*                                                                            *)
(*    Lemma BER_to_bitstring_correct (scaled : bool) (f : BER_float) :        *)
(*    correct_bitstring (BER_to_bitstring scaled f) = true.                   *)
(*  Proof.                                                                    *)
(*    unfold BER_to_bitstring.                                                *)
(*    repeat break_match; try reflexivity.                                    *)
(*    unfold finite_BER_to_bitstring.                                         *)
(*    break_match.                                                            *)
(*    - (* short *)                                                           *)
(*      unfold correct_bitstring.                                             *)
(*      admit.                                                                *)
(*    - (* long *)                                                            *)
(*  Admitted.                                                                 *)
(******************************************************************************)

Theorem BER_bitstring_roundtrip (scaled : bool) (f : BER_float) :
  roundtrip_option
    BER_float BER_bitstring BER_float
    BER_to_bitstring
    bitstring_to_BER
    BER_float_strict_eqb
    f.
Admitted.
(***************************************************************************)
(* Proof.                                                                  *)
(*   unfold roundtrip_option, Some_ize.                                    *)
(*   simpl. intros H. clear H.                                             *)
(*   unfold bool_het_inverse'. simpl.                                      *)
(*   break_match.                                                          *)
(*   - (* pass *)                                                          *)
(*     destruct f.                                                         *)
(*     + (* zero *)                                                        *)
(*       destruct s; simpl in *; inversion Heqo; reflexivity.              *)
(*     + (* infinity *)                                                    *)
(*       destruct s; simpl in *; inversion Heqo; reflexivity.              *)
(*     + (* nan *)                                                         *)
(*       inversion Heqo. reflexivity.                                      *)
(*     + (* finite *)                                                      *)
(*       simpl in *.                                                       *)
(*       unfold finite_BER_to_bitstring in Heqo.                           *)
(*       destruct (twos_olen e <? 4)%Z.                                    *)
(*       * (* long exponent *)                                             *)
(*         simpl in *.                                                     *)
(*         destruct valid_short_sumbool eqn:VS; try some_eq_none_inv.      *)
(*         inversion Heqo as [H]. clear Heqo.                              *)
(*         rewrite sign2bits_inv.                                          *)
(*                                                                         *)
(*         (* radix needs to be correct to be invertable *)                *)
(*         inversion e0 as [BV].                                           *)
(*         unfold valid_BER in BV.                                         *)
(*         apply andb_prop in BV. inversion BV as [B V]. clear B.          *)
(*         rewrite (radix2bits_inv b0 V).                                  *)
(*                                                                         *)
(*         rewrite signif2bits_inv.                                        *)
(*                                                                         *)
(*         remember (twos_olen e) as toe.                                  *)
(*         assert (T : (toe - 1 + 1 = toe)%Z) by ring.                     *)
(*         rewrite T.                                                      *)
(*         rewrite exp2bits_inv.                                           *)
(*                                                                         *)
(*         rewrite e0.                                                     *)
(*                                                                         *)
(*         reflexivity.                                                    *)
(*       * (* short exponent *)                                            *)
(*         simpl in *.                                                     *)
(*         destruct valid_long_sumbool eqn:VS; try some_eq_none_inv.       *)
(*         inversion Heqo as [H]. clear Heqo.                              *)
(*         rewrite sign2bits_inv.                                          *)
(*                                                                         *)
(*         (* radix needs to be correct to be invertable *)                *)
(*         inversion e0 as [BV].                                           *)
(*         unfold valid_BER in BV.                                         *)
(*         apply andb_prop in BV. inversion BV as [B V]. clear B.          *)
(*         rewrite (radix2bits_inv b0 V).                                  *)
(*                                                                         *)
(*         rewrite signif2bits_inv.                                        *)
(*         rewrite exp2bits_inv.                                           *)
(*         rewrite e0.                                                     *)
(*         reflexivity.                                                    *)
(*   - (* no pass *)                                                       *)
(*     exfalso.                                                            *)
(*     generalize dependent (BER_to_bitstring_correct scaled f). intros C. *)
(*     unfold bitstring_to_BER in Heqo.                                    *)
(*                                                                         *)
(*     destruct BER_to_bitstring eqn:BB.                                   *)
(*                                                                         *)
(*     + (* special *)                                                     *)
(*       destruct classify_BER eqn:H.                                      *)
(*       * break_match; try some_eq_none_inv.                              *)
(*       * simpl in C.                                                     *)
(*         unfold valid_special in C.                                      *)
(*         rewrite H in C.                                                 *)
(*         inversion C.                                                    *)
(*                                                                         *)
(*     + (* short *)                                                       *)
(*       destruct valid_short_sumbool.                                     *)
(*       * some_eq_none_inv.                                               *)
(*       * clear Heqo.                                                     *)
(*         unfold correct_bitstring in C.                                  *)
(*         rewrite e in C. inversion C.                                    *)
(*                                                                         *)
(*     + (* long *)                                                        *)
(*       destruct valid_long_sumbool.                                      *)
(*       * some_eq_none_inv.                                               *)
(*       * clear Heqo.                                                     *)
(*         unfold correct_bitstring in C.                                  *)
(*         rewrite e in C. inversion C.                                    *)
(* Qed.                                                                    *)
(***************************************************************************)