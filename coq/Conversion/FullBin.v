Require Import ZArith Basics.
Require Import ASN.ASNDef Conversion.ASN_Bin Conversion.ASN_IEEE Aux.Option Aux.StructTactics.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Open Scope Z.

Definition l1 {A B : Type} (f : A -> option B) : (option A -> option B) :=
  fun oa : option A =>
    match oa with
    | Some a => f a
    | None => None
    end.

Definition l2 {A B : Type} (f : A -> B) : (option A -> option B) :=
  fun oa : option A =>
    match oa with
    | Some a => Some (f a)
    | None => None
    end.

    

Section B32.

  Let prec := 24.
  Let emax := 128.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  
  Definition b32_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition b32_to_BER_binary : Z -> option Z :=
    compose (l2 (BER_to_bits false)) (compose b32_to_BER_abstract b32_of_bits).

  Definition BER_to_b32_abstract := BER_to_IEEE_exact prec emax prec_gt_1.

  Definition BER_to_b32_binary : Z -> option Z :=
    compose (l2 bits_of_b32) (compose (l1 BER_to_b32_abstract) bits_to_BER).

End B32.


Section B64.

  Let prec := 53.
  Let emax := 1024.
  Let prec_gt_1 : Prec_gt_1 prec.
  Proof. reflexivity. Qed.
  
  Definition b64_to_BER_abstract := IEEE_to_BER_exact prec emax.

  Definition b64_to_BER_binary : Z -> option Z :=
    compose (l2 (BER_to_bits false)) (compose b32_to_BER_abstract b32_of_bits).

  Definition BER_to_b64_abstract := BER_to_IEEE_exact prec emax prec_gt_1.

  Definition BER_to_b64 : Z -> option Z :=
    compose (l2 bits_of_b32) (compose (l1 BER_to_b32_abstract) bits_to_BER).

End B64.
