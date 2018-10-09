Require Import PArith Sumbool.
Require Import ASN1FP.ASN.ASNDef.
Require Import Flocq.Core.Zaux.

Definition valid_BER_sumbool (m : positive) (e : Z) (b : radix) :=
  sumbool_of_bool (valid_BER m e b).

