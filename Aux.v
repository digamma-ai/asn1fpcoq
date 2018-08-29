
(* Monadic `bind` operation for `option` Monad *)
Definition option_bind
           {A B: Type} (f: A -> option B) : (option A -> option B) :=
  fun oa => match oa with
         | Some a => f a
         | None => None
         end.

(* Monadic `liftM2` operation for `option` Monad *)
Definition option_liftM2
           {A B C: Type} (f: A -> B -> C) : (option A -> option B -> option C) :=
  fun oa ob => match oa, ob with
         | Some a, Some b => Some (f a b)
         | _, _ => None
         end.

Definition is_None_b {A : Type} (x : option A) : bool :=
  match x with
  | None => true
  | _ => false
  end.

Definition is_Some_b {A : Type} (x : option A) : bool :=
  match x with
  | Some _ => true
  | _ => false
  end.
