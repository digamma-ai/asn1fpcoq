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
