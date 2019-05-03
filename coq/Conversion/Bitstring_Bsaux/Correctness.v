Require Import ZArith Lia.
Require Import ProofIrrelevance.
Require Import ASN1FP.Types.Bitstring ASN1FP.Types.BSaux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Types.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option
        ASN1FP.Conversion.Bitstring_Bsaux.Definitions.




(** * roundtrip *)

Definition Some_ize {A B : Type} : (A -> B) -> (A -> option B)
  := Basics.compose Some.

Lemma special_eqb_refl (val : BER_special) :
  special_eqb val val = true.
Proof. destruct val; reflexivity. Qed.
  
Theorem bitstring_bsaux_roundtrip (b : BER_bitstring) :
  roundtrip_option
      BER_bitstring BER_bs_aux BER_bitstring
      (Some_ize bsaux_of_bitstring)
      (Some_ize bitstring_of_bsaux)
      BER_bitstring_eqb
      b.
Proof.
  (* basic simplification *)
  unfold roundtrip_option.
  intros H; clear H.
  unfold bool_het_inverse'; simpl.

  unfold bitstring_of_bsaux, bsaux_of_bitstring.
  repeat break_match; inversion Heqb0; subst.
  - simpl. rewrite special_eqb_refl. reflexivity.
  - clear H7 H8.
    unfold c2z, c2n; simpl.
    inversion Heqb0; subst.
    repeat apply inj_pair2 in H0.
    repeat apply inj_pair2 in H1.
    rewrite <- H0, <- H1.
    simpl.
    repeat rewrite Z.eqb_refl.
    reflexivity.
  - 
    unfold c2z, c2n; simpl.
    inversion Heqb0; subst.
    repeat apply inj_pair2 in H0.
    repeat apply inj_pair2 in H1.
    rewrite <- H0, <- H1.
    simpl.
    repeat rewrite Z.eqb_refl.
    reflexivity.
Qed.
