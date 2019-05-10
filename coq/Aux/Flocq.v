Require Import ZArith Lia Basics.
Require Import Flocq.IEEE754.Binary.

Open Scope Z.

Section Flocq_bounded_IEEE.
 
  Let log2 := log_inf.
  Let digits := compose Z.succ log2.
  
  Lemma digits2_pos_log2 (m : positive) :
    Z.pos (Digits.digits2_pos m) = Z.succ (log2 m).
  Proof.
    induction m; simpl; try (rewrite Pos2Z.inj_succ, IHm); reflexivity.
  Qed.
  
  Lemma digits2_pos_digits (m : positive) :
    Z.pos (Digits.digits2_pos m) = digits m.
  Proof.
    unfold digits, compose.
    apply digits2_pos_log2.
  Qed.
  
  (** ** Flocq's Binary.bounded rewritten in a form close to IEEE-754 *)
  Lemma bounded_unfolded (prec emax : Z)
        (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec) (Hmax : (prec < emax)%Z)
        (m : positive) (e : Z) :
    let emin := 3 - emax - prec in
    bounded prec emax m e = true
    <->
    or
      (digits m < prec /\ e = emin)
      (digits m = prec /\ emin <= e <= emax - prec).
  Proof.
    intro.
    unfold FLX.Prec_gt_0, bounded, canonical_mantissa, FLT.FLT_exp in *.
    rewrite Bool.andb_true_iff, Z.leb_le, <-Zeq_is_eq_bool, digits2_pos_digits.
    split; intro.
    all: destruct (Z_lt_le_dec (digits m + e - prec) emin).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: lia.
  Qed.

End Flocq_bounded_IEEE.
