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

Definition option_filer {T : Type} (P : bool) : T -> option T :=
  fun x => if P then Some x else None.