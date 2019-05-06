Require Import ZArith Basics.
Require Import ASN1FP.Aux.Option
               ASN1FP.Types.ASN
               ASN1FP.Conversion.IEEE_ASN
               ASN1FP.Conversion.ASN_Bitstring
               ASN1FP.Conversion.Bitstring_Bsaux
               ASN1FP.Conversion.Bsaux_Bits.
Require Import ASN1FP.Conversion.Full.Abstract.

Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation. Local Open Scope monad_scope.

Open Scope Z.
Open Scope program_scope.

Notation "f <=< g" := (g >=> f) (at level 50).

Search (Z -> Z).

(* TODO: radix, scaling *)
(* extraction-ready functions for the most common IEEE formats *)
Section B32.

  Definition float32_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
    ret ∘ bits_of_bsaux ∘ bsaux_of_bitstring <=< bitstring_of_BER <=<
        BER_of_b32_abstract ∘ b32_of_bits.

  Definition BER_to_float32_exact : Z -> option Z :=
    ret ∘ bits_of_b32 <=< b32_of_BER_abstract_exact <=<
        BER_of_bitstring ∘ bitstring_of_bsaux <=< bsaux_of_bits.

  Definition BER_to_float32_rounded (rounding: mode) : Z -> option Z :=
    ret ∘ bits_of_b32 <=< (b32_of_BER_abstract_rounded rounding) <=<
        BER_of_bitstring ∘ bitstring_of_bsaux <=< bsaux_of_bits.

  Definition normalize_float32 (m e : Z) : Z * Z :=
    normalize_b32_abstract m e.

End B32.

Section B64.

  Definition float64_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
    ret ∘ bits_of_bsaux ∘ bsaux_of_bitstring <=< bitstring_of_BER <=<
        BER_of_b64_abstract ∘ b64_of_bits.

  Definition BER_to_float64_exact : Z -> option Z :=
    ret ∘ bits_of_b64 <=< b64_of_BER_abstract_exact <=<
        BER_of_bitstring ∘ bitstring_of_bsaux <=< bsaux_of_bits.

  Definition BER_to_float64_rounded (rounding: mode) : Z -> option Z :=
    ret ∘ bits_of_b64 <=< (b64_of_BER_abstract_rounded rounding) <=<
        BER_of_bitstring ∘ bitstring_of_bsaux <=< bsaux_of_bits.

  Definition normalize_float64 (m e : Z) : Z * Z :=
    normalize_b64_abstract m e.

End B64.
