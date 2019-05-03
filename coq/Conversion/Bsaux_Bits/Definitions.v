Require Import ZArith Lia.
Require Import ProofIrrelevance.
Require Import ASN1FP.Types.Bitstring ASN1FP.Types.BSaux
        ASN1FP.Aux.Roundtrip ASN1FP.Aux.Bits
        ASN1FP.Aux.StructTactics ASN1FP.Types.BitContainer
        ASN1FP.Aux.Tactics ASN1FP.Aux.Option.
Require Import ASN1FP.Conversion.Bitstring_Bsaux.Definitions.

(** * lengths *)

Definition info_nblen := 24%nat.

Definition nbs_nblen (b : BER_nbs) : nat :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ => 8 * (c2n co + 2)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ => 8 * (c2n co + 2)
  end.

Definition content_nblen (b : BER_nbs) : nat :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ => 8 * (c2n co - 1)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ => 8 * (c2n co - 1)
  end.

Lemma short_nblen_correct {l1 l2 : nat} (co : container l1) (ee : container l2)
  (m : container (8 * (c2n co - c2n ee - 2))) :
    (8 * (c2n ee + 1) + 8 * (c2n co - c2n ee - 2))%nat = (8 * (c2n co - 1))%nat.
Proof.
  destruct co, ee, m; rename v into co, v0 into ee, v1 into m.
  uncont; clear L L0 N N0 l1 l2.
  generalize (nblen_positive m); intros.
  lia.
Qed.

Lemma long_nblen_correct {l1 l2 : nat} (co : container l1) (eo : container l2)
  (m : container (8 * (c2n co - c2n eo - 2))) :
    (8 + (8 * c2n eo + 8 * (c2n co - c2n eo - 2)))%nat = (8 * (c2n co - 1))%nat.
Proof.
  destruct co, eo, m; rename v into co, v0 into eo, v1 into m.
  uncont; clear L L0 N N0 l1 l2.
  generalize (nblen_positive m); intros.
  lia.
Qed.

Lemma nbs_nblen_correct (b : BER_nbs) :
  (info_nblen + content_nblen b)%nat = nbs_nblen b.
Proof.
  generalize (nbs_co_positive b).
  destruct b;
    unfold nbs_co, content_nblen, nbs_nblen, info_nblen;
    lia.
Qed.

Definition BER_nblen (b : Z) : nat :=
  let l := nblen b in
  l + (l mod 8)%nat.

Lemma BER_nblen_correct (b : Z) :
  (nblen b <= BER_nblen b)%nat.
Proof. unfold BER_nblen; lia. Qed.

Definition bsaux_nblen (b : BER_bs_aux) :=
  match b with
  | special_aux val => nblen (bits_of_special val)
  | normal_aux b => nbs_nblen b
  end.
 


(** * nbs -> cont *)

Definition mk_info (b : BER_nbs) : container info_nblen :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ =>
       join_cont id
      (join_cont co
      (join_cont t
      (join_cont s
      (join_cont bb
      (join_cont ff ee
       )))))
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ =>
       join_cont id
      (join_cont co
      (join_cont t
      (join_cont s
      (join_cont bb
      (join_cont ff ee
       )))))
  end.

Definition append_info {l : nat} (b : BER_nbs) (c : container l) :=
  join_cont (mk_info b) c.

Definition mk_content (b : BER_nbs) : container (content_nblen b) :=
  match b with
  | short_nbs id co t s bb ff ee e m _ _ _ _ _ =>
    cast_cont (join_cont e m) (short_nblen_correct co ee m)
  | long_nbs id co t s bb ff ee eo e m _ _ _ _ _ =>
    cast_cont (join_cont eo (join_cont e m)) (long_nblen_correct co eo m)
  end.

Definition cont_of_nbs (b : BER_nbs) : container (nbs_nblen b) :=
  cast_cont (append_info b (mk_content b)) (nbs_nblen_correct b).



(** * cont -> nbs *)

Fact info_nblen_positive : (0 < info_nblen)%nat.
Proof. unfold info_nblen. lia. Qed.

Definition cut_info {l : nat} (c : container (info_nblen + l)) (L : (0 < l)%nat) :
  (container info_nblen * container l) :=
  split_cont c info_nblen_positive L.

Fact ilc1 : (0 < info_nblen - 8)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc2 : (0 < info_nblen - 8 - 8)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc3 : (0 < info_nblen - 8 - 8 - 1)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc4 : (0 < info_nblen - 8 - 8 - 1 - 1)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc5 : (0 < info_nblen - 8 - 8 - 1 - 1 - 2)%nat.
Proof. unfold info_nblen. lia. Qed.

Fact ilc6 : (0 < info_nblen - 8 - 8 - 1 - 1 - 2 - 2)%nat.
Proof. unfold info_nblen. lia. Qed.

Program Definition split_info (c : container info_nblen) :
  (cont8 * cont8 * cont1 * cont1 * cont2 * cont2 * cont2) :=
  let '(id, c)  := cut_b8_cont c ilc1 in
  let '(co, c)  := cut_b8_cont c ilc2 in
  let '(t,  c)  := cut_b1_cont c ilc3 in
  let '(s,  c)  := cut_b1_cont c ilc4 in
  let '(bb, c)  := cut_b2_cont c ilc5 in
  let '(ff, ee) := cut_b2_cont c ilc6 in
  (id, co, t, s, bb, ff, ee).

(* TODO: would be nice to clean this *)

Definition split_cut_info {l : nat} (c : container (info_nblen + l)) (L : (0 < l)%nat) :=
  let '(info, content) := cut_info c L in
  let '(id, co, t, s, bb, ff, ee) := split_info info in
  (id, co, t, s, bb, ff, ee, content).

Definition e_nblen_of_long_cont {l : nat} (c : container (8 + l)) (L : (0 < l)%nat) : nat :=
  c2n (fst (cut_b8_cont c L)).

Definition try_cut_num (a b : nat) : option (a = b + (a - b))%nat :=
  match (Nat.eq_dec a (b + (a - b))) with
  | right _ => None
  | left H => Some H
  end.

Lemma try_cut_num_works (a b : nat) (L : (0 < a - b)%nat) :
  is_Some_b (try_cut_num a b) = true.
Proof.
  unfold try_cut_num.
  destruct (Nat.eq_dec a (b + (a - b))); simpl.
  reflexivity.
  lia.
Qed.

Definition cut_num (a b : nat) (L : (0 < a - b)%nat) :
  (a = b + (a - b))%nat.
{
  generalize (try_cut_num_works a b L); intros.
  destruct (try_cut_num a b).
  exact e.
  inversion H.
} Defined.

Definition cut_cont {l : nat} (c : container l) (l1 : nat) (L : (0 < l - l1)%nat)
  : container (l1 + (l - l1)) :=
  cast_cont c (cut_num l l1 L).
  
Definition try_cut_cont {l : nat} (c : container l) (l1 : nat)
  : option (container (l1 + (l - l1))) :=
    match le_lt_dec l1 0 with
    | left _ => None
    | right L1 =>
      match le_lt_dec (l - l1) 0 with
      | left _ => None
      | right L2 =>
      Some ((cut_cont c l1 L2))
      end
    end.

Definition try_split_cont {l : nat} (c : container l) (l1 : nat) :=
    match le_lt_dec l1 0 with
    | left _ => None
    | right L1 =>
      match le_lt_dec (l - l1) 0 with
      | left _ => None
      | right L2 =>
      Some (split_cont (cut_cont c l1 L2) L1 L2)
      end
    end.

Definition try_split_long_cont  {l : nat} (c : container (8 + l)) (L : (0 < l)%nat)
  : option (container 8 *
            container (e_nblen_of_long_cont c L) *
            container (l - e_nblen_of_long_cont c L)) :=
    let eo := fst (cut_b8_cont c L) in
    let em := snd (cut_b8_cont c L) in
    let eon := c2n eo in
    match try_split_cont em eon with
    | None => None
    | Some (e,m) =>
      Some (eo, e, m)
    end.

Definition check_short_elen {l : nat} (ee : cont2) (e : container l) :=
  match Nat.eq_dec l (8 * (c2n ee + 1)) with
  | right _ => None
  | left E => Some (cast_cont e E)
  end.

Definition check_long_elen {l : nat} (eo : cont8) (e : container l) :=
  match Nat.eq_dec l (8 * (c2n eo)) with
  | right _ => None
  | left E => Some (cast_cont e E)
  end.

Definition check_short_mlen {l : nat} (co : cont8) (ee : cont2) (m : container l) :=
  match Nat.eq_dec l (8 * (c2n co - c2n ee - 2)) with
  | right _ => None
  | left M => Some (cast_cont m M)
  end.

Definition check_long_mlen {l : nat} (co : cont8) (eo : cont8) (m : container l) :=
  match Nat.eq_dec l (8 * (c2n co - c2n eo - 2)) with
  | right _ => None
  | left M => Some (cast_cont m M)
  end.

Definition construct_short_nbs
           {l1 l2 : nat}
           (id co : cont8)
           (t s : cont1) (bb ff ee : cont2)
           (e : container l1) (m : container l2)
  : option BER_nbs :=
  match (check_short_elen ee e) with
  | None => None
  | Some e =>
    match (check_short_mlen co ee m) with
    | None => None
    | Some m =>
      match Z.eq_dec (c2z id) real_id_b with
      | right _ => None
      | left VS1 =>
        match Z.eq_dec (c2z t) 1 with
        | right _ => None
        | left VS2 =>
          match Z_le_dec (c2z ee) 2 with
          | right _ => None
          | left VS3 =>
            match Z_le_dec 1 (c2z m) with
            | right _ => None
            | left VS4 =>
              match Z_le_dec (c2z co) 127 with
              | right _ => None
              | left VS5 =>
              Some (short_nbs id co t s bb ff ee e m VS1 VS2 VS3 VS4 VS5)
              end
            end
          end
        end
      end
    end
  end.

Definition construct_long_nbs
           { l1 l2 : nat }
           (id co : cont8)
           (t s : cont1) (bb ff ee : cont2)
           (eo : cont8)
           (e : container l1) (m : container l2)
  : option BER_nbs :=
  match (check_long_elen eo e) with
  | None => None
  | Some e =>
    match (check_long_mlen co eo m) with
    | None => None
    | Some m =>
      match Z.eq_dec (c2z id) real_id_b with
      | right _ => None
      | left VL1 =>
        match Z.eq_dec (c2z t) 1 with
        | right _ => None
        | left VL2 =>
          match Z.eq_dec (c2z ee) 3 with
          | right _ => None
          | left VL3 =>
            match Z_le_dec 1 (c2z m) with
            | right _ => None
            | left VL4 =>
              match Z_le_dec (c2z co) 127 with
              | right _ => None
              | left VL5 =>
               Some (long_nbs id co t s bb ff ee eo e m VL1 VL2 VL3 VL4 VL5)
              end
            end
          end
        end
      end
    end
  end.

Definition nbs_of_cont {l : nat} (c : container l) :=
  match (try_cut_cont c info_nblen) with
  | None => None
  | Some c =>
    match le_lt_dec (l - info_nblen) 0 with
    | left _ => None
    | right L =>
      let '(id, co, t, s, bb, ff, ee, content) := split_cut_info c L in
      if (c2n ee =? 3)%nat
      then match (try_cut_cont content 8) with
           | None => None
           | Some content =>
             match le_lt_dec (l - info_nblen - 8) 0 with
             | left _ => None
             | right L =>
               match (try_split_long_cont content L) with
               | None => None
               | Some (eo, e, m) =>
                   construct_long_nbs id co t s bb ff ee eo e m
               end
             end
           end
      else match (try_split_cont content (8 * (c2n ee + 1))) with
           | None => None
           | Some (e, m) =>
               construct_short_nbs id co t s bb ff ee e m
           end
    end
  end.

(** * bsaux <-> cont *)

Lemma bits_of_special_nonneg (val : BER_special) :
  0 <= bits_of_special val.
Proof.
  destruct val; simpl.
  unfold pzero_b; lia.
  unfold nzero_b; lia.
  unfold pinf_b; lia.
  unfold ninf_b; lia.
  unfold nan_b; lia.
Qed.

Definition cont_of_bsaux (b : BER_bs_aux) : container (bsaux_nblen b) :=
  match b with
  | special_aux val =>
    let zval := bits_of_special val in
    cont (nblen zval) zval (bits_of_special_nonneg val) (Nat.le_refl (nblen zval))
  | normal_aux b => cont_of_nbs b
  end.


(** * cont <-> Z *)

Definition cont_of_BER_bits (b : Z) : option (container (BER_nblen b)) :=
  match (Z_gt_le_dec 0 b) with
  | left _ => None
  | right N => Some (cont (BER_nblen b) b N (BER_nblen_correct b))
  end.
  
Definition Z_of_bsaux (b : BER_bs_aux) :=
  c2z (cont_of_bsaux b).

Definition bits_of_bitstring (b : BER_bitstring) : Z :=
  Z_of_bsaux (bsaux_of_bitstring b).

Definition mk_special_bsaux (b : Z) : option BER_bs_aux :=
  match classify_BER b with
  | Some pzero => Some (special_aux pzero)
  | Some nzero => Some (special_aux nzero)
  | Some pinf  => Some (special_aux pinf)
  | Some ninf  => Some (special_aux ninf)
  | Some nan   => Some (special_aux nan)
  | None       => None
  end.

Definition bsaux_of_bits (b : Z) : option BER_bs_aux :=
  if b <? 0
  then None
  else match (mk_special_bsaux b) with
       | Some b => Some b
       | None =>
         match cont_of_BER_bits b with
         | None => None
         | Some c =>
           match (nbs_of_cont c) with
           | None => None
           | Some b => Some (normal_aux b)
           end
         end
       end.

Definition bitstring_of_bits (b : Z) : option BER_bitstring :=
  match bsaux_of_bits b with
  | None => None
  | Some b => Some (bitstring_of_bsaux b)
  end.
