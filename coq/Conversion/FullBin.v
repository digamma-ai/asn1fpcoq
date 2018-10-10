Require Import ZArith Basics.
Require Import ASN.ASNDef  Conversion.ASN_Bin Conversion.ASN_IEEE Aux.StructTactics Aux.BinK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Open Scope Z.

Section B32.

  Definition float32_to_BER_exact (f:Z): option Z :=
    ab <- b32_to_BER_abstract (b32_of_bits f) ;;
       ret (BER_to_bits false ab).

  Definition BER_to_float32_exact (asn:Z): option Z :=
    bf <- bits_to_BER asn ;;
       af <- BER_to_b32_abstract_exact bf ;;
       ret (bits_of_b32 af).

  Definition BER_to_float32_rounded (rounding: mode) (asn:Z): option Z :=
    bf <- bits_to_BER asn ;;
       af <- BER_to_b32_abstract_rounded rounding bf ;;
       ret (bits_of_b32 af).

End B32.


Section B64.

    Definition float64_to_BER_exact (f: Z): option Z :=
    ab <- b64_to_BER_abstract (b64_of_bits f) ;;
       ret (BER_to_bits false ab).

    Definition BER_to_float64_exact (asn: Z): option Z :=
    bf <- bits_to_BER asn ;;
       af <- BER_to_b64_abstract_exact bf ;;
       ret (bits_of_b64 af).

    Definition BER_to_float64rounded (rounding : mode ) (asn:Z): option Z :=
    bf <- bits_to_BER asn ;;
       af <- BER_to_b64_abstract_rounded rounding bf ;;
       ret (bits_of_b64 af).

End B64.