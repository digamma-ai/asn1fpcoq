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

Definition l1 {A B : Type} (f : A -> option B) : (option A -> option B) :=
  fun oa : option A =>
    match oa with
    | Some a => f a
    | None => None
    end.

Definition l2 {A B : Type} (f : A -> B) : (option A -> option B) :=
  fun oa : option A =>
    match oa with
    | Some a => Some (f a)
    | None => None
    end.