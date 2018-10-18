Require Import ZArith.
Require Import ASN1FP.Types.ASNDef ASN1FP.Types.BitstringDef
        ASN1FP.Aux.Bits ASN1FP.Aux.Tactics ASN1FP.Aux.StructTactics
        ASN1FP.Conversion.ASN_Bitstring.Atomic.

Require Import Lia.

Require Import Flocq.Core.Zaux.

  (* TODO: scaling *)
  Definition finite_BER_to_bitstring
             (scaled : bool) (s : bool) (b : radix) (m : positive) (e : Z) : BER_bitstring :=
    let m := signif2bits m in
    let s := sign2bits s in
    let bb := radix2bits b in
    let ff := 0%Z in
    let e_olen := twos_olen e in let e := exp2bits e_olen e in
      if Z.ltb (e_olen) 4
      then short real_id_b (e_olen + olen m + 1)%Z 1 s bb ff (e_olen - 1)        e m
      else long  real_id_b (e_olen + olen m + 2)%Z 1 s bb ff            3 e_olen e m.

  Definition BER_to_bitstring (scaled : bool) (f : BER_float) : BER_bitstring :=
    match f with
    | BER_zero s => if s then special nzero_b else special pzero_b
    | BER_infinity s => if s then special ninf_b else special pinf_b
    | BER_nan => special nan_b
    | BER_finite s b m e _ => finite_BER_to_bitstring scaled s b m e
    end.

  Definition valid_short_sumbool (id co t s bb ff ee e m : Z) :=
    Sumbool.sumbool_of_bool (valid_short id co t s bb ff ee e m).

  Definition valid_long_sumbool (id co t s bb ff ee eo e m : Z) :=
    Sumbool.sumbool_of_bool (valid_long id co t s bb ff ee eo e m).

  (* TEMPORARILY HERE TO RESOLVE CIRCULAR DEPENDENCY *)
 (*****) Lemma Zlt_Zle (a b : Z) :
 (*****)   a < b <-> a <= b - 1.
 (*****) Proof. lia. Qed.

 (*****) Lemma not_Zlt_Zle (a b : Z) :
 (*****)   ~ a < b <-> b <= a.
 (*****) Proof. lia. Qed.
 (*****)  

 (*****) Lemma valid_short_valid_BER {id co t s bb ff ee e m : Z} :
 (*****)   valid_short id co t s bb ff ee e m = true ->
 (*****)   valid_BER (bits2signif m) (bits2exp (ee + 1) e) (bits2radix bb) = true.
 (*****) Proof.
 (*****)   unfold valid_short. intros H.
 (*****)   unfold valid_BER. apply andb_true_intro. split.
 (*****)   unfold correct_short_co in H.
 (*****)   repeat split_andb; rewrite Z.ltb_lt in *; rewrite Z.eqb_eq in *.
 (*****)   remember (ee+1) as eeo eqn:EEO.
 (*****)   clear H0 H6 H7 H8 H9 H10 H11 H12.
 (*****)   try rewrite Zlt_Zle in *.
 (*****)   apply (Z.le_trans (eeo + olen m) (co - 1) 126) in H; try lia.
 (*****)   apply (Z.le_trans (olen e) (ee+2-1) 3) in H3; try lia.
 (*****)   (* - (* bounded *) *)
 (*****)   (*   unfold bounded. *)
 (*****)   (*   break_match; rewrite Z.ltb_lt in *. *)
 (*****)   (*   + (* long *) *)
 (*****)   (*     contradict Heqb. *)
 (*****)   (*     rewrite not_Zlt_Zle. *)
 (*****)   (*     unfold bits2exp. *)
 (*****)   (*     admit. *)
 (*****)       


 (*****)   (*   + (* short *) *)
 (*****)   (*     unfold bits2signif; rewrite Z2Pos.id. *)
 (*****)   (*     rewrite Z.ltb_ge in Heqb. *)
 (*****) Admitted.

 (*****) Lemma valid_long_valid_BER {id co t s bb ff ee eo e m : Z} :
 (*****)   valid_long id co t s bb ff ee eo e m = true ->
 (*****)   valid_BER (bits2signif m) (bits2exp (eo) e) (bits2radix bb) = true.
 (*****) Admitted.
 (*****) 
 (*****)   Lemma BER_to_bitstring_correct (scaled : bool) (f : BER_float) :
 (*****)   correct_bitstring (BER_to_bitstring scaled f) = true.
 (*****) Proof.
 (*****)   unfold BER_to_bitstring.
 (*****)   repeat break_match; try reflexivity.
 (*****)   unfold finite_BER_to_bitstring.
 (*****)   break_match.
 (*****)   - (* short *)
 (*****)     unfold correct_bitstring.
 (*****)     admit.
 (*****)   - (* long *)
 (*****) Admitted.


  (* default garbage return in BER_nan *)
  Definition bitstring_to_BER (b : BER_bitstring) : option BER_float :=
    match b with
    | special val =>
      match classify_BER val with
      | Some pzero => Some (BER_zero false)
      | Some nzero => Some (BER_zero true)
      | Some pinf => Some (BER_infinity false)
      | Some ninf => Some (BER_infinity true)
      | Some nan => Some (BER_nan)
      | None => None
      end

    | short id co t s bb ff ee e m =>
      match valid_short_sumbool id co t s bb ff ee e m with
      | right _ => None
      | left V =>
        Some (BER_finite
                (bits2sign s)
                (bits2radix bb)
                (bits2signif m)
                (bits2exp (ee + 1) e)
                (valid_short_valid_BER V)
             )
      end

    | long  id co t s bb ff ee eo e m =>
      match valid_long_sumbool id co t s bb ff ee eo e m with
      | right _ => None
      | left V =>
        Some (BER_finite
                (bits2sign s)
                (bits2radix bb)
                (bits2signif m)
                (bits2exp (eo) e)
                (valid_long_valid_BER V)
             )
      end
    end.
