Require Import ZArith Basics.
Require Import ASN.ASNDef  Conversion.ASN_Bin Conversion.ASN_IEEE Aux.Option Aux.StructTactics Aux.binK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Open Scope Z.

Section B32.

  Definition b32_to_BER_binary : Z -> option Z :=
    compose (l2 (BER_to_bits false)) (compose b32_to_BER_abstract b32_of_bits).

  Definition BER_to_b32_binary : Z -> option Z :=
    compose (l2 bits_of_b32) (compose (l1 BER_to_b32_abstract) bits_to_BER).

End B32.


Section B64.

  Definition b64_to_BER_binary : Z -> option Z :=
    compose (l2 (BER_to_bits false)) (compose b32_to_BER_abstract b32_of_bits).

  Definition BER_to_b64 : Z -> option Z :=
    compose (l2 bits_of_b32) (compose (l1 BER_to_b32_abstract) bits_to_BER).

End B64.
