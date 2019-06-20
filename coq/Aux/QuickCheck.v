Require Import ZArith PArith Lia List String.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.IEEE754.Bits.
Require Import ASN1FP.Aux.Roundtrip ASN1FP.Conversion.Full.Extracted.
Require Import ASN1FP.Conversion.IEEE_ASN.
Require Import ASN1FP.Aux.Flocq.
Require Import ASN1FP.Aux.StructTactics.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Open Scope Z.

Open Scope string.

Instance show_binary : Show (binary_float 24 128) := {
  show c := match c with
              | B754_zero false => "+zero"
              | B754_zero true => "-zero"
              | B754_infinity false => "+inf"
              | B754_infinity true => "-inf"
              | B754_nan false _ _ => "+nan"
              | B754_nan true _ _ => "-nan"
              | B754_finite s m e _ => (if s then "+" else "-")
                                        ++ (show_Z (Z.pos m))
                                        ++ (show_Z e)
            end
}.

Close Scope string.

Definition zerg := 
  (liftGen (fun (s : bool) => B754_zero 24 128 s)) 
    (choose (true, false)).
Definition infg := 
  (liftGen (fun (s : bool) => B754_infinity 24 128 s))
    (choose (true, false)).

Lemma nan1 : nan_pl 24 1%positive = true.
Proof. auto. Qed.

Definition nang := 
  (liftGen (fun b => B754_nan 24 128 b 1%positive nan1))
    (choose (true, false)).

Definition boundaries (t : bool) :=
  let r := 
      if t 
      then (1, 2^24 - 1, -149, -149)%Z 
      else (2^23, 2^24 - 1, -149, 104)%Z 
  in r.

Definition choose_from_boundaries (t : G bool) : G (Z * Z) :=
  bindGen' ((fmap boundaries) t) (fun '(m_min, m_max, e_min, e_max) =>
  fun b1 =>
    bindGen' (choose (m_min, m_max)) (fun (m : Z) => fun b2 =>
      bindGen' (choose (e_min, e_max)) (fun (e : Z) => fun b3 =>
        returnGen (m, e)))).

Program Definition fing : G (binary_float 24 128) :=
  bindGen' (choose (false, true)) (fun t => fun b0 => 
    bindGen' (returnGen (boundaries t)) 
    (fun '(m_min, m_max, e_min, e_max) => fun b1 =>
      bindGen' (choose (false, true)) (fun (s : bool) => fun b2 =>
        bindGen' (choose (m_min, m_max)) (fun (m : Z) => fun b3 =>
          bindGen' (choose (e_min, e_max)) (fun (e : Z) => fun b4 =>
            returnGen (B754_finite 24 128 s (Z.to_pos m) e _)))))).
Next Obligation.
  (* get rid of technical junk *)
  clear s b0 b2; rename b3 into b2, b4 into b3.
  apply semReturn in b1.
  apply semChoose in b2.
  apply semChoose in b3.
  all: unfold is_true, set1, boundaries in *.

  (* simplify *)
  apply andb_prop in b2; destruct b2 as [B11 B12].
  apply andb_prop in b3; destruct b3 as [B21 B22].
  all: destruct t; try tuple_inversion; try rewrite Z.leb_le in *.

  (* solve easy subgoals *)
  3,4,5: lia.
  3: rewrite Z.pow_pos_fold; lia.

  (* simplify for main subgoals *)
  all: assert (T : m < 16777216) by lia; clear B12; rename T into B12.
  all: replace 16777216 with (2 ^ 24) in B12 by reflexivity.
  all: rewrite bounded_unfolded; unfold FLX.Prec_gt_0, Basics.compose, Z.succ; try lia.

  (* solve 1 *)
  replace (log_inf (Z.to_pos m)) with (Z.log2 m).
  rewrite Z.log2_lt_pow2 in B12; lia.
  destruct m; try lia.
  rewrite Zlog2_log_inf.
  reflexivity.

  (* solve 2 *)
  right.
  rewrite Z.pow_pos_fold in B11.
  assert (MP : 0 < m) by lia.
  rewrite Z.log2_le_pow2 in B11 by lia.
  rewrite Z.log2_lt_pow2 in B12 by lia.
  replace (log_inf (Z.to_pos m)) with (Z.log2 m).
  lia.
  destruct m; try lia.
  rewrite Zlog2_log_inf.
  reflexivity.
Qed.

Import ListNotations.

Definition binary32_gen : G (binary_float 24 128) :=
  freq_ zerg [(1, zerg)%nat ; (1, infg)%nat ; (1, nang)%nat ; (7, fing)%nat].

Definition binary_float_BER_exact_roundtrip (b32 : binary_float 24 128) : bool
  := roundtrip_bool
       (binary_float 24 128) Z (binary_float 24 128)
       (float32_to_BER_exact radix2 false)
       BER_to_float32_exact
       float_eqb_nan_t
       b32.

QuickChick (forAll binary32_gen binary_float_BER_exact_roundtrip).

Close Scope Z.
