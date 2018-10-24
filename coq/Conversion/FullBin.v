Require Import ZArith Basics.
Require Import Aux.Option
        Types.ASNDef
        Conversion.IEEE_ASN.Def
        Conversion.ASN_Bitstring.Def
        Conversion.Bitstring_Bits.Def
        Conversion.BinK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Open Scope Z.

(* Left-to-right composition of Kleisli arrows. *)
Notation "f >=> g" := (fun x => pbind (f x) g) (at level 50, left associativity) : monad_scope.

Section B32.
  Definition float32_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
    option_filer (target_radix =? 2)%Z >=>
      compose b32_to_BER_abstract b32_of_bits >=> (BER_to_bitstring scaled) >=>
      compose ret bitstring_to_bits.

  Definition BER_to_float32_exact: Z -> option Z :=
    bits_to_bitstring >=> bitstring_to_BER >=> BER_to_b32_abstract_exact >=>
             compose ret bits_of_b32.

  Definition BER_to_float32_rounded (rounding: mode): Z -> option Z :=
    bits_to_bitstring >=> bitstring_to_BER >=> BER_to_b32_abstract_rounded rounding >=>
             compose ret bits_of_b32.
End B32.

Section B64.

  Definition float64_to_BER_exact (target_radix : radix) (scaled : bool) : Z -> option Z :=
    option_filer (target_radix =? 2)%Z >=>
    compose b64_to_BER_abstract b64_of_bits >=> (BER_to_bitstring scaled) >=>
    compose ret bitstring_to_bits.

  Definition BER_to_float64_exact: Z -> option Z :=
    bits_to_bitstring >=> bitstring_to_BER >=> BER_to_b64_abstract_exact >=>
             compose ret bits_of_b64.

  Definition BER_to_float64_rounded (rounding: mode): Z -> option Z :=
    bits_to_bitstring >=> bitstring_to_BER >=> BER_to_b64_abstract_rounded rounding >=>
             compose ret bits_of_b64.
End B64.