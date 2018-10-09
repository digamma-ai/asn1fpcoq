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

Lemma inv_trans {A1 A2 B C : Type}
      {f1 : A1 -> B} {b1 : B -> A2} {ea : A1 -> A2 -> bool}
      {f2 : B -> C} {b2 : C -> B} {eb : B -> B -> bool}
      {x : A1} :
      (forall (y z : B), eb y z = true -> b1 y = b1 z) ->
      bool_het_inverse A1 B A2 f1 b1 ea x ->
      bool_het_inverse B C B f2 b2 eb (f1 x) ->
      bool_het_inverse A1 C A2 (compose f2 f1) (compose b1 b2) ea x.
Proof.
  unfold bool_het_inverse, compose.
  intros H H1 H2.
  apply H in H2.
  rewrite <- H2.
  apply H1.
Qed.
