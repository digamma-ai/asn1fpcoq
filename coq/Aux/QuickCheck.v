Require Import ZArith PArith Lia.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.IEEE754.Bits.
Require Import ASN1FP.Aux.Roundtrip ASN1FP.Conversion.Full.Extracted.
Require Import ASN1FP.Conversion.IEEE_ASN.
Require Import ASN1FP.Aux.Flocq.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Open Scope Z.

Require Import String. Open Scope string.

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

Definition fing := binary_gen (choose (true, false)).

Require Import List.
Import ListNotations.

Definition binary32_gen : G (option (binary_float 24 128)) :=
  freq_ zerg [(1, zerg)%nat ; (1, infg)%nat ; (1, nang)%nat ; (7, fing)%nat].

Definition binary_float_eqb {prec emax : Z} (a1 a2 : binary_float prec emax) :=
  match a1, a2 with
  | B754_nan _ _ _, B754_nan _ _ _ => true
  | _,_ =>
    match Bcompare prec emax a1 a2 with
    | Some cmp => match cmp with
                 | Eq => true
                 | _ => false
                 end
    | None => false
    end
  end.

Definition binary_float_BER_exact_roundtrip (b32 : binary_float 24 128) : bool
  := roundtrip_bool
       (binary_float 24 128) ASN.BER_float (binary_float 24 128)
       (BER_of_IEEE_exact 24 128)
       Abstract.b32_of_BER_abstract_exact
       binary_float_eqb
       b32.

QuickChick (forAllMaybe binary32_gen binary_float_BER_exact_roundtrip).

Close Scope Z.
