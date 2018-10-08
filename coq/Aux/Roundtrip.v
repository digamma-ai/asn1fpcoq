Require Import Coq.Program.Basics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import ASN1FP.Aux.Option.

Import MonadNotation.
Local Open Scope monad_scope.

(*
  `b` is invers of `f` wrt. heterogenous equality `e`
 *)
Definition bool_het_inverse
           (A1 B A2 : Type)
           (f: A1 -> B)
           (b: B -> A2)
           (e: A1 -> A2 -> bool)
           (x: A1)
: Prop :=
  e x (b (f x)) = true.

(* monadic version of `bool_het_inverse` *)
Definition bool_het_inverse'
           (m: Type -> Type)
           `{Monad m}
           (A1 B A2 : Type)
           (f: A1 -> m B)
           (b: B -> m A2)
           (e: A1 -> A2 -> bool)
           (x: A1)
  : m bool:=
  y <- f x ;;
    x' <- b y ;;
    ret (e x x').

(*
  "Round-trip" converting between types A1, B, A2:
  A1 -> B -> A2

  if
    forward pass happens
  then
      backward pass happens
    and
      backward pass returns an element,
      equivalent to the starting one
*)
Definition roundtrip_option
           (A1 B A2 : Type)
           (f: A1 -> option B) (* forward pass *)
           (b: B -> option A2) (* backward pass *)
           (e: A1 -> A2 -> bool) (* equivalence on A *)
           (x: A1) (* value *)
  : Prop :=
   is_Some_b (f x) = true ->
   bool_het_inverse' option A1 B A2 f b e x = Some true.