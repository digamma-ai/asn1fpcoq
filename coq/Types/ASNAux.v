Require Import PArith.
Require Import ASN1FP.Types.ASNDef.
Require Import Flocq.Core.Zaux.

Definition valid_BER_sumbool (m : positive) (e : Z) (b : radix) :=
  Sumbool.sumbool_of_bool (valid_BER m e b).
