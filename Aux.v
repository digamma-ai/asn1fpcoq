Definition option_bind
           {A B: Type} (f: A -> option B) : (option A -> option B) :=
  fun oa => match oa with
         | Some a => f a
         | None => None
         end.

Definition bin_bool_option_bind {A B: Type} (f: A -> B -> bool) : (option A -> option B -> bool) :=
  fun oa ob => match oa, ob with
             | None, None => true
             | Some a, Some b => f a b
             | _ , _ => false
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