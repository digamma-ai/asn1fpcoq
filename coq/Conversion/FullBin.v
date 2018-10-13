Require Import ZArith Basics.
Require Import ASN.ASNDef  Conversion.ASN_Bin Conversion.ASN_IEEE Aux.StructTactics Aux.BinK.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Open Scope Z.

(* Left-to-right composition of Kleisli arrows. *)
Notation "f >=> g" := (fun x => pbind (f x) g) (at level 50, left associativity) : monad_scope.

Section B32.

  Definition float32_to_BER_exact: Z -> option Z :=
    compose b32_to_BER_abstract b32_of_bits >=> compose ret (BER_to_bits false).

  Definition BER_to_float32_exact: Z -> option Z :=
    bits_to_BER >=> BER_to_b32_abstract_exact >=> compose ret bits_of_b32.

  Definition BER_to_float32_rounded (rounding: mode): Z -> option Z :=
    bits_to_BER >=> BER_to_b32_abstract_rounded rounding >=>
                compose ret bits_of_b32.
End B32.


Section B64.

  Definition float64_to_BER_exact: Z -> option Z :=
    compose b64_to_BER_abstract b64_of_bits >=> compose ret (BER_to_bits false).

  Definition BER_to_float64_exact: Z -> option Z :=
    bits_to_BER >=> BER_to_b64_abstract_exact >=> compose ret bits_of_b64.

  Definition BER_to_float64_rounded (rounding: mode): Z -> option Z :=
    bits_to_BER >=> BER_to_b64_abstract_rounded rounding >=>
                compose ret bits_of_b64.

End B64.