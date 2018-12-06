Definition curry {A B C : Type} (f : (A * B) -> C) (x : A) (y : B) :=
  f (x, y).

Definition uncurry {A B C : Type} (g : A -> B -> C) (t : A * B) :=
  let '(x, y) := t in g x y.