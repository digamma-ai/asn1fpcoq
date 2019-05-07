Require Import ZArith.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.IEEE754.Bits.
Require Import ASN1FP.Aux.Roundtrip ASN1FP.Conversion.Full.Extracted.
Require Import ASN1FP.Conversion.IEEE_ASN.

Open Scope Z.

Definition float_eqb (b1 : Z) (b2 : Z) : bool :=
  float_eqb_nan_t (b32_of_bits b1) (b32_of_bits b2).

Theorem float32_BER_exact_roundtirp (b32 : Z) :
  roundtrip_option
    Z Z Z
    (float32_to_BER_exact radix2 false)
    BER_to_float32_exact
    float_eqb
    b32.
Admitted.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

QuickChick float32_BER_exact_roundtirp.

Close Scope Z.
