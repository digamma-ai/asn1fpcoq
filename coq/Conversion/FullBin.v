Require Import ZArith Basics.
Require Import Aux.Option
        Types.ASNDef
        Conversion.IEEE_ASN.DefProof
        Conversion.ASN_Bitstring.Def
        Conversion.Bitstring_Bits.Def
        Conversion.BinK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation. Local Open Scope monad_scope.

Open Scope Z.

(* TODO: radix, scaling *)
(* extraction-ready functions for the most common IEEE formats *)
Section B32.

  Definition float32_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
      compose (BER_of_b32_abstract) b32_of_bits >=> bitstring_of_BER >=>
      compose ret bits_of_bitstring.

  Definition BER_to_float32_exact: Z -> option Z :=
    bitstring_of_bits >=> BER_of_bitstring >=> b32_of_BER_abstract_exact >=>
             compose ret bits_of_b32.

  Definition BER_to_float32_rounded (rounding: mode): Z -> option Z :=
    bitstring_of_bits >=> BER_of_bitstring >=> b32_of_BER_abstract_rounded rounding >=>
             compose ret bits_of_b32.

  Definition normalize_float32 (m e : Z) : Z * Z :=
    normalize_b32_abstract m e.

End B32.

Section B64.

  Definition float64_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
      compose (BER_of_b64_abstract) b64_of_bits >=> bitstring_of_BER >=>
      compose ret bits_of_bitstring.

  Definition BER_to_float64_exact: Z -> option Z :=
    bitstring_of_bits >=> BER_of_bitstring >=> b64_of_BER_abstract_exact >=>
             compose ret bits_of_b64.

  Definition BER_to_float64_rounded (rounding: mode): Z -> option Z :=
    bitstring_of_bits >=> BER_of_bitstring >=> b64_of_BER_abstract_rounded rounding >=>
             compose ret bits_of_b64.

  Definition normalize_float64 (m e : Z) : Z * Z :=
    normalize_b64_abstract m e.

End B64.