Require Import ZArith PArith Lia.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.IEEE754.Bits.
Require Import ASN1FP.Aux.Roundtrip ASN1FP.Conversion.Full.Extracted.
Require Import ASN1FP.Conversion.IEEE_ASN.
Require Import ASN1FP.Aux.Flocq.

Require Import List.
Import ListNotations.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Open Scope Z.
Definition float_eqb (b1 : Z) (b2 : Z) : bool :=
  float_eqb_nan_t (b32_of_bits b1) (b32_of_bits b2).

Theorem float32_BER_exact_roundtrip (b32 : Z) : roundtrip_option
    Z Z Z
    (float32_to_BER_exact radix2 false)
    BER_to_float32_exact
    float_eqb
    b32.
Admitted.

QuickChick float32_BER_exact_roundtrip. 

Definition min0 := -1000000.
Definition max0 :=  1000000.
Definition min1 := -6000000000.
Definition max1 := -5000000000.
Definition min2 := 5000000000.
Definition max2 := 6000000000.

(*
QuickChick (forAll (choose (min0, max0)) (fun t => collect (show t) true)).
QuickChick (forAll (choose (min1, max1)) (fun t => collect (show t) true)).
QuickChick (forAll (choose (min2, max2)) (fun t => collect (show t) true)). 
*)

Require Import String. Open Scope string.

Instance show_binary : Show (binary_float 24 128) := {
  show c := match c with
              | B754_zero _ _ false => "+zero"
              | B754_zero _ _ true => "-zero"
              | B754_infinity _ _ false => "+inf"
              | B754_infinity _ _ true => "-inf"
              | B754_nan _ _ false _ _ => "+nan"
              | B754_nan _ _ true _ _ => "-nan"
              | B754_finite _ _ s m e _ => (if s then "+" else "-") 
                                           ++ (show_Z (Z.pos m))
                                           ++ (show_Z e)
            end
}.

(*
  Lemma bounded_unfolded (prec emax : Z)
        (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec) (Hmax : (prec < emax)%Z)
        (m : positive) (e : Z) :
    let emin := 3 - emax - prec in
    bounded prec emax m e = true
    <->
    or
      (digits m < prec /\ e = emin)
      (digits m = prec /\ emin <= e <= emax - prec).
*)

Fact prec_gt_0 : 0 < 24.
Proof. reflexivity. Qed.

Fact prec_lt_emax: 24 < 128.
Proof. reflexivity. Qed.

Definition bounded_24_128 := 
  bounded_unfolded 24 128 prec_gt_0 prec_lt_emax.

Theorem bounded_24_128' : forall (m : positive) (e : Z),
    e = -149 /\ (Z.pos m < 2 ^ 24)
    \/
    -149 <= e <= 104 /\ (2 ^ 23 <= Z.pos m < 2 ^ 24)
    -> bounded 24 128 m e = true.
Proof.
  intros m e M.
  apply (bounded_unfolded 24 128 prec_gt_0 prec_lt_emax).
  destruct M as [M1 | M1]; destruct M1 as [E M].
  all: unfold Basics.compose, Z.succ; simpl.
  all: rewrite <-Zlog2_log_inf.
  - 
    assert (Z.log2 (Z.pos m) + 1 < 24 <-> Z.log2 (Z.pos m) < 23) 
      as Z by lia.
    assert (Z.log2 (Z.pos m) + 1 = 24 <-> Z.log2 (Z.pos m) = 23)
      as Z1 by lia.
    rewrite Z, Z1.
    rewrite Z.log2_lt_pow2 in M.
    lia.
    reflexivity.
  - 
    assert (Z.log2 (Z.pos m) + 1 < 24 <-> Z.log2 (Z.pos m) < 23) 
      as Z by lia.
    assert (Z.log2 (Z.pos m) + 1 = 24 <-> Z.log2 (Z.pos m) = 23)
      as Z1 by lia.
    rewrite Z, Z1.
    destruct M as [M1 M2].
    rewrite Z.log2_lt_pow2 in M2.
    rewrite Z.log2_le_pow2 in M1.
    lia.
    reflexivity.
    reflexivity.
Qed.

(*
e = -149 /\ m E (1, 2^24)
\/
-149 <= e <= 104 /\ m E [2^23, 2^24)
*)

Definition zerg := 
  (liftGen (fun (s : bool) => Some (B754_zero 24 128 s))) 
    (choose (true, false)).
Definition infg := 
  (liftGen (fun (s : bool) => Some (B754_infinity 24 128 s))) 
    (choose (true, false)).

Lemma nan1 : nan_pl 24 1%positive = true.
Proof. auto. Qed.

Definition nang := 
  (liftGen (fun b => Some (B754_nan 24 128 b 1%positive nan1))) 
    (choose (true, false)).


Definition boundaries (t : bool) :=
  let r := 
      if t 
      then (1, 2^24 - 1, -149, -149)%Z 
      else (2^23, 2^24 - 1, -149, 104)%Z 
  in r.

Theorem boundaries_right : forall (s : bool), 
    boundaries s = (1, 2^24 - 1, -149, -149)%Z
                                            \/
    boundaries s = (2^23, 2^24 - 1, -149, 104)%Z.
Proof. 
  intros. 
  unfold boundaries.
  case s.
  left.
  reflexivity.
  right.
  reflexivity.
Qed.

Definition getPos (z : Z) : positive :=
  match z with
    | Z0 => 1
    | Zpos p => p
    | Zneg p => p
  end.

(*
Program Definition gen_test' (t : G bool) : G (binary_float 24 128) :=
  bindGen ((fmap boundaries) t) (fun '(m_min, m_max, e_min, e_max) =>
    bindGen (choose (true, false)) (fun (s : bool) =>
      bindGen (choose (m_min, m_max)) (fun (m : Z) =>
        bindGen (choose (e_min, e_max)) (fun (e : Z) =>
          returnGen (
                  B754_finite 24 128 s (getPos m) e _
              ))))).

Next Obligation.
*)

Definition binary_gen (t : G bool) : G (option (binary_float 24 128)) :=
  bindGen ((fmap boundaries) t) (fun '(m_min, m_max, e_min, e_max) =>
    bindGen (choose (true, false)) (fun (s : bool) =>
      bindGen (choose (m_min, m_max)) (fun (m : Z) =>
        bindGen (choose (e_min, e_max)) (fun (e : Z) =>
          returnGen (
              match binary_bounded_sumbool 24 128 (getPos m) e with
                | left bbs_true => 
                  Some (B754_finite 24 128 s (getPos m) e bbs_true)
                | right _ => None
              end))))).

Sample (binary_gen (choose (true, false))).

Definition fing := binary_gen (choose (true, false)).

Definition binary32_gen : G (option (binary_float 24 128)) :=
  freq_ zerg [(1, zerg)%nat ; 
              (1, infg)%nat ; 
              (1, nang)%nat ; 
              (7, fing)%nat].

Definition binary_float_eqb {prec emax : Z} (a1 a2 : binary_float prec emax) :=
  match Bcompare prec emax a1 a2 with
    | Some cmp => match cmp with
                   | Eq => true
                   | _ => false
                 end
    | None => false
  end. 

Definition binary_float_BER_exact_roundtrip (b32 : binary_float 24 128) : Prop := roundtrip_option
    (binary_float 24 128) ASN.BER_float (binary_float 24 128)
    (BER_of_IEEE_exact 24 128)
    Abstract.b32_of_BER_abstract_exact
    binary_float_eqb
    b32.

Global Instance dec_prop : forall (b : binary_float 24 128), Dec (binary_float_BER_exact_roundtrip b).
Proof.
  intros b.
  split.
  unfold ssrbool.decidable,
         binary_float_BER_exact_roundtrip,
         roundtrip_option,
         Option.is_Some_b,
         bool_het_inverse'.
  destruct (BER_of_IEEE_exact 24 128).
Admitted.

Global Instance dec_bin : forall (b : binary_float 24 128), Checkable (binary_float_BER_exact_roundtrip b).
Proof.
Admitted.

SearchAbout "testDec".

QuickChick (forAllMaybe binary32_gen binary_float_BER_exact_roundtrip).

Close Scope Z.
