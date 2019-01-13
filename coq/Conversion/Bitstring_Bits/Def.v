Require Import ZArith.
Require Import ASN1FP.Types.BitstringDef
               ASN1FP.Aux.Bits ASN1FP.Aux.BitContainer ASN1FP.Aux.Tactics.
Require Import Lia.

Open Scope Z.

Let z2n := Z.to_nat.

(* subject to change *)
Definition bitstring_nblen (b : BER_bitstring) : nat :=
  match b with
  | special val => nblen (Z.abs val)
  | short _ co _ _ _ _ ee _ _ _ 
    => (8 + (8 + (1 + (1 + (2 + (2 + (2 + (z2n (8 * (ee + 1)) + z2n (8 * (co - ee - 2))))))))))
  | long _ co _ _ _ _ _ eo _ _ _
    => (8 + (8 + (1 + (1 + (2 + (2 + (2 + (8 +(z2n (8 * eo) + z2n (8 * (co - eo - 2)))))))))))
  end.

(*
Lemma short_bitstring_nblen_correct {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (8 + (8 + (1 + (1 + (2 + (2 + (2 + (z2n (8 * (ee + 1)) + z2n (8 * (co - ee - 2))))))))))%nat
  = bitstring_nblen (short id co t s bb ff ee e m VS).
Proof. reflexivity. Qed.

Lemma long_bitstring_nblen_correct {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (8 + (8 + (1 + (1 + (2 + (2 + (2 + (8 +(z2n (8 * eo) + z2n (8 * (co - eo - 2)))))))))))%nat
  = bitstring_nblen (long id co t s bb ff ee eo e m VL).
Proof. reflexivity. Qed.
*)

(*
Definition b8_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 8)%nat)
  : container 8 := cont 8 v N L.

Definition b2_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 2)%nat)
  : container 2 := cont 2 v N L.

Definition b1_cont (v : Z) (N : 0 <= v) (L : (nblen v <= 1)%nat)
  : container 1 := cont 1 v N L.
*)

Ltac deVS :=
  unfold valid_short, real_id_b in *; repeat split_andb; debool; subst.

Ltac deVL :=
  unfold valid_long, real_id_b in *; repeat split_andb; debool; subst.


(** * id *)
Lemma VS_id_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= id.
Proof. deVS; lia. Qed.

Lemma VS_id_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen id <= 8)%nat.
Proof. deVS; unfold nblen; simpl; lia. Qed.

Lemma VL_id_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= id.
Proof. deVL; lia. Qed.

Lemma VL_id_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen id <= 8)%nat.
Proof. deVL; unfold nblen; simpl; lia. Qed.

(** * co *)
Lemma VS_co_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= co.
Proof. deVS; lia. Qed.

Lemma VS_co_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen co <= 8)%nat.
Admitted.

Lemma VL_co_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= co.
Proof. deVL; lia. Qed.

Lemma VL_co_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen co <= 8)%nat.
Admitted.

(** * t *)
Lemma VS_t_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= t.
Proof. deVS; lia. Qed.

Lemma VS_t_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen t <= 1)%nat.
Admitted.

Lemma VL_t_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= t.
Proof. deVL; lia. Qed.

Lemma VL_t_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen t <= 1)%nat.
Admitted.

(** * s *)
Lemma VS_s_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= s.
Proof. deVS; lia. Qed.

Lemma VS_s_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen s <= 1)%nat.
Admitted.

Lemma VL_s_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= s.
Proof. deVL; lia. Qed.

Lemma VL_s_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen s <= 1)%nat.
Admitted.

(** * bb *)
Lemma VS_bb_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= bb.
Proof. deVS; lia. Qed.

Lemma VS_bb_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen bb <= 2)%nat.
Admitted.

Lemma VL_bb_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= bb.
Proof. deVL; lia. Qed.

Lemma VL_bb_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen bb <= 2)%nat.
Admitted.

(** * ff *)
Lemma VS_ff_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= ff.
Proof. deVS; lia. Qed.

Lemma VS_ff_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen ff <= 2)%nat.
Admitted.

Lemma VL_ff_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= ff.
Proof. deVL; lia. Qed.

Lemma VL_ff_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen ff <= 2)%nat.
Admitted.

(** * ee *)
Lemma VS_ee_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= ee.
Proof. deVS; lia. Qed.

Lemma VS_ee_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen ee <= 2)%nat.
Admitted.

Lemma VL_ee_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= ee.
Proof. deVL; lia. Qed.

Lemma VL_ee_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen ee <= 2)%nat.
Admitted.

(** * eo *)
Lemma VL_eo_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= eo.
Proof. deVL; lia. Qed.

Lemma VL_eo_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen eo <= 8)%nat.
Admitted.

(** * e *)
Lemma VS_e_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= e.
Proof. deVS; lia. Qed.

Lemma VS_e_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen e <= z2n (8*(ee + 1)))%nat.
Admitted.

Lemma VL_e_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= e.
Proof. deVL; lia. Qed.

Lemma VL_e_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen e <= z2n (8*eo))%nat.
Admitted.

(** * m *)
Lemma VS_m_N {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  0 <= m.
Proof. deVS; lia. Qed.

Lemma VS_m_L {id co t s bb ff ee e m : Z}
      (VS : valid_short id co t s bb ff ee e m = true) :
  (nblen m <= z2n (8*(co - ee - 2)))%nat.
Admitted.

Lemma VL_m_N {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  0 <= m.
Proof. deVL; lia. Qed.

Lemma VL_m_L {id co t s bb ff ee eo e m : Z}
      (VL : valid_long id co t s bb ff ee eo e m = true) :
  (nblen m <= z2n (8*(co - eo - 2)))%nat.
Admitted.

Fact tmpaux1 : 0 <= 0. Proof. reflexivity. Qed.
Fact tmpaux2 : (nblen 0 <= 17)%nat. Proof. unfold nblen. simpl. lia. Qed.

Fact nblen_cont_len (v : Z) :
  (nblen v <= nblen v)%nat.
Proof. reflexivity. Qed.

Definition cont_of_bitstring (b : BER_bitstring) : container (bitstring_nblen b) :=
  match b with
  | special val =>
    let v := Z.abs val in
    cont (nblen v) v (Z.abs_nonneg val) (nblen_cont_len v)
  | short id co t s bb ff ee e m VS =>
      join_cont
        (cont 8 id (VS_id_N VS) (VS_id_L VS))
      (join_cont
        (cont 8 co (VS_co_N VS) (VS_co_L VS))
      (join_cont
        (cont 1 t (VS_t_N VS) (VS_t_L VS))
      (join_cont
        (cont 1 s (VS_s_N VS) (VS_s_L VS))
      (join_cont
        (cont 2 bb (VS_bb_N VS) (VS_bb_L VS))
      (join_cont
        (cont 2 ff (VS_ff_N VS) (VS_ff_L VS))
      (join_cont
        (cont 2 ee (VS_ee_N VS) (VS_ee_L VS))
      (join_cont
        (cont (z2n (8*(ee+1))) e (VS_e_N VS) (VS_e_L VS))
      (cont (z2n (8*(co - ee - 2))) m (VS_m_N VS) (VS_m_L VS)
      ))))))))
  | long id co t s bb ff ee eo e m VL => 
      join_cont
        (cont 8 id (VL_id_N VL) (VL_id_L VL))
      (join_cont
        (cont 8 co (VL_co_N VL) (VL_co_L VL))
      (join_cont
        (cont 1 t (VL_t_N VL) (VL_t_L VL))
      (join_cont
        (cont 1 s (VL_s_N VL) (VL_s_L VL))
      (join_cont
        (cont 2 bb (VL_bb_N VL) (VL_bb_L VL))
      (join_cont
        (cont 2 ff (VL_ff_N VL) (VL_ff_L VL))
      (join_cont
        (cont 2 ee (VL_ee_N VL) (VL_ee_L VL))
      (join_cont
        (cont 8 eo (VL_eo_N VL) (VL_eo_L VL))
      (join_cont
        (cont (z2n (8*eo)) e (VL_e_N VL) (VL_e_L VL))
      (cont (z2n (8*(co - eo - 2))) m (VL_m_N VL) (VL_m_L VL)
      )))))))))
  end.

Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  Z_of_cont (cont_of_bitstring b).

(*
Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  match b with
  | special val =>
    match classify_BER val with
    | Some pzero => pzero_b
    | Some nzero => nzero_b
    | Some pinf => pinf_b
    | Some ninf => ninf_b
    | Some nan => nan_b
    | None => -1
    end

  | short id content_olen type sign base scaling exp_olen_b exponent significand _ =>
    let em_olen := content_olen - 1 in
    let em_blen := 8*em_olen in
    join_octets_ext (content_olen + 1) id
      (join_octets_ext content_olen content_olen

        (join_bits_ext (em_blen + 7) type
          (join_bits_ext (em_blen + 6) sign
            (join_bits_ext (em_blen + 4) base
              (join_bits_ext (em_blen + 2) scaling

                (join_octets_ext em_olen exp_olen_b
                  (join_octets_ext (em_olen - exp_olen_b - 1) exponent
                    significand)))))))


  | long id content_olen type sign base scaling lexp exp_olen_o exponent significand _ =>
    let em_olen := content_olen - 2 in
    let lem_blen := 8*(em_olen+1) in
    join_octets_ext (content_olen + 1) id
      (join_octets_ext content_olen content_olen

        (join_bits_ext (lem_blen + 7) type
          (join_bits_ext (lem_blen + 6) sign
            (join_bits_ext (lem_blen + 4) base
              (join_bits_ext (lem_blen + 2) scaling
                (join_octets_ext (em_olen + 1) lexp

                  (join_octets_ext em_olen exp_olen_o
                    (join_octets_ext (em_olen - exp_olen_o) exponent
                      significand))))))))
  end.
*)

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match classify_BER b with
    | Some pzero => Some (special pzero_b)
    | Some nzero => Some (special nzero_b)
    | Some pinf => Some (special pinf_b)
    | Some ninf => Some (special ninf_b)
    | Some nan => Some (special nan_b)
    | None =>
      let '(id, co_content) := split_octets_by_fst 1 b in
      let '(co, content) := split_octets_by_fst 1 co_content in
      let '(tsbbffee, l_exp_signif) := split_octets_by_fst 1 content in
      let '(t, sbbffee) := split_bits_by_snd 7 tsbbffee in
      let '(s, bbffee) := split_bits_by_snd 6 sbbffee in
      let '(bb, ffee) := split_bits_by_snd 4 bbffee in
      let '(ff, ee) := split_bits_by_snd 2 ffee in
      if (2 <? ee)
      then
        let '(e_olen, exp_signif) := split_octets_by_fst 1 l_exp_signif in
        let '(exp, signif) := split_octets_by_snd (co - e_olen - 2) exp_signif in
        match valid_long_sumbool id co t s bb ff ee e_olen exp signif with
          | right _ => None
          | left V => Some (long id co t s bb ff ee e_olen exp signif V)
        end
      else
        let '(exp, signif) := split_octets_by_snd (co - ee - 2) l_exp_signif in
        match valid_short_sumbool id co t s bb ff ee exp signif with
          | right _ => None
          | left V => Some (short id co t s bb ff ee exp signif V)
        end
    end.