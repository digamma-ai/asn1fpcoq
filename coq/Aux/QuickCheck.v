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

Instance show_binary : forall (prec emax : Z), Show (binary_float prec emax) := {
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

Definition binary32 := binary_float 24 128.
Definition binary64 := binary_float 53 1024.

Definition zerg (prec emax : Z) := 
  (liftGen (fun (s : bool) => B754_zero prec emax s)) 
    (choose (true, false)).
Definition infg (prec emax : Z) := 
  (liftGen (fun (s : bool) => B754_infinity prec emax s))
    (choose (true, false)).

Lemma nan1 : nan_pl 24 1%positive = true.
Proof. auto. Qed.

Definition nang (prec emax : Z) (np : nan_pl prec 1 = true) :=
  (liftGen (fun b => B754_nan prec emax b 1%positive np))
    (choose (true, false)).

Definition boundaries (prec emax : Z) (t : bool) :=
      if t 
      then (1, 2^prec - 1, 3 - emax - prec, 3 - emax - prec)%Z 
      else (2^(prec - 1), 2^prec - 1, 3 - emax - prec, emax - prec)%Z.

Program Definition fing (prec emax : Z) : G (binary_float prec emax) :=
  bindGen' (choose (false, true)) (fun t => fun b0 => 
    bindGen' (returnGen (boundaries prec emax t)) 
    (fun '(m_min, m_max, e_min, e_max) => fun b1 =>
      bindGen' (choose (false, true)) (fun (s : bool) => fun b2 =>
        bindGen' (choose (m_min, m_max)) (fun (m : Z) => fun b3 =>
          bindGen' (choose (e_min, e_max)) (fun (e : Z) => fun b4 =>
            returnGen (B754_finite prec emax s (Z.to_pos m) e _)))))).
Next Obligation.
  (* get rid of technical junk *)
  (* clear s b0 b2; rename b3 into b2, b4 into b3.
  apply semReturn in b1.
  apply semChoose in b2.
  apply semChoose in b3.
  all: unfold is_true, set1, boundaries in *.

  (* simplify *)
  apply andb_prop in b2; destruct b2 as [B11 B12].
  apply andb_prop in b3; destruct b3 as [B21 B22].
  all: destruct t; try rewrite Z.leb_le in *.
  all: tuple_inversion.

  (* solve easy subgoals *)
  - admit.
  - admit.
  3,4,5: lia.
  3: rewrite Z.pow_pos_fold; lia.

  (* simplify for main subgoals *)
  all: assert (T : m < 16777216) by lia; clear B12; rename T into B12.
  all: replace 16777216 with (2 ^ 24) in B12 by reflexivity.
  all: rewrite bounded_unfolded; unfold FLX.Prec_gt_0, Basics.compose, Z.succ; try lia. (* solve 1 *)
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
Qed. *)
Admitted.

Import ListNotations.

Definition zerg32 := zerg 24 128.
Definition infg32 := infg 24 128.
Definition nang32 := nang 24 128 nan1.
Definition fing32 := fing 24 128.

Definition binary32_gen : G (binary32) :=
  freq_ zerg32 [(1, zerg32)%nat ; (1, infg32)%nat ;
                (1, nang32)%nat ; (7, fing32)%nat].

Definition binary_float32_BER_exact_roundtrip (b32 : binary32) : bool
  := roundtrip_bool
       (binary32) Z (binary32)
       (float32_to_BER_exact radix2 false)
       BER_to_float32_exact
       float_eqb_nan_t
       b32.

QuickChick (forAll binary32_gen binary_float32_BER_exact_roundtrip).

Definition zerg64 := zerg 53 1024.
Definition infg64 := infg 53 1024.
Definition nang64 := nang 53 1024 nan1.
Definition fing64 := fing 53 1024.

Definition binary64_gen : G (binary64) :=
  freq_ zerg64 [(1, zerg64)%nat ; (1, infg64)%nat ;
                (1, nang64)%nat ; (7, fing64)%nat].

Definition binary_float64_BER_exact_roundtrip (b64 : binary64) : bool
  := roundtrip_bool
       (binary64) Z (binary64)
       (float64_to_BER_exact radix2 false)
       BER_to_float64_exact
       float_eqb_nan_t
       b64.

QuickChick (forAll binary64_gen binary_float64_BER_exact_roundtrip).

Close Scope Z.
