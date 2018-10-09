Require Import ZArith Basics.
Require Import ASN.ASNDef  Conversion.ASN_Bin Conversion.ASN_IEEE Aux.Option Aux.StructTactics Aux.BinK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Open Scope Z.

Section B32.

    Definition b32_to_BER_binary_exact : Z -> option Z :=
      compose (l2 (BER_to_bits false)) (compose b32_to_BER_abstract b32_of_bits).

    Definition BER_to_b32_binary_exact : Z -> option Z :=
      compose (l2 bits_of_b32) (compose (l1 BER_to_b32_abstract_exact) bits_to_BER).

    Definition BER_to_b32_binary_rounded (rounding : mode ) : Z -> option Z :=
      compose (l2 bits_of_b32)
        (compose (l1 (BER_to_b32_abstract_rounded rounding))
          bits_to_BER).

End B32.


Section B64.

    Definition b64_to_BER_binary_exact : Z -> option Z :=
      compose (l2 (BER_to_bits false)) (compose b64_to_BER_abstract b64_of_bits).

    Definition BER_to_b64_binary_exact : Z -> option Z :=
      compose (l2 bits_of_b64) (compose (l1 BER_to_b64_abstract_exact) bits_to_BER).

    Definition BER_to_b64_binary_rounded (rounding : mode ) : Z -> option Z :=
      compose (l2 bits_of_b64)
        (compose (l1 (BER_to_b64_abstract_rounded rounding))
          bits_to_BER).

End B64.