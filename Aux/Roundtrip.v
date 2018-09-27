Require Import Aux.Option.

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
Definition roundtrip
           (A1 B A2 : Type)
           (f: A1 -> option B) (* forward pass *)
           (b: B -> option A2) (* backward pass *)
           (e: A1 -> A2 -> bool) (* equivalence on A *)
           (x: A1) (* value *)
  : Prop :=
    is_Some_b (f x) = true ->
    option_liftM2 e (Some x) (option_bind b (f x)) = Some true.



Definition roundtrip'
           (A1 B A2 : Type)
           (f: A1 -> B)
           (b: B -> A2)
           (e: A1 -> A2 -> bool)
           (x: A1)
: Prop :=
  e x (b (f x)) = true.

Definition roundtrip_option'
           (A1 B A2 : Type)
           (f: A1 -> option B) (* forward pass *)
           (b: B -> option A2) (* backward pass *)
           (e: A1 -> A2 -> bool) (* equivalence on A *)
           (x: A1) (* value *)
  : Prop :=
  let oe := fun a1 oa2 => match oa2 with | Some a2 => e a1 a2 | None => false end in
    is_Some_b (f x) = true ->
    roundtrip'
      A1 (option B) (option A2)
      f
      (option_bind b)
      oe
      x.
