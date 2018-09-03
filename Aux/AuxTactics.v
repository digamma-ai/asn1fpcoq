Require Import ZArith PArith.

Ltac some_eq_none_inv :=
  match goal with
  | [ H: Some _ = None |- _ ] => inversion H
  | [ H: None = Some _ |- _ ] => inversion H
  end.

Ltac true_eq_false_inv :=
  match goal with
  | [ H: true = false |- _ ] => inversion H
  | [ H: false = true |- _ ] => inversion H
  end.

Ltac some_inv :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H
  end.

Ltac check_contradiction :=
  match goal with
  | [ H1: ?P = true, H2 : ?P = false |- _ ] => rewrite -> H1 in H2; inversion H2
  end.

Ltac compare_nrefl :=
  match goal with
  | [ H: (Z.compare ?z ?z) = Lt |- _ ] => rewrite -> Z.compare_refl in H; inversion H
  | [ H: (Z.compare ?z ?z) = Gt |- _ ] => rewrite -> Z.compare_refl in H; inversion H
  | [ H: (Pos.compare ?p ?p) = Lt |- _ ] => rewrite -> Pos.compare_refl in H; inversion H
  | [ H: (Pos.compare ?p ?p) = Gt |- _ ] => rewrite -> Pos.compare_refl in H; inversion H
  | [ H: _ (Pos.compare_cont Eq ?p ?p) = Lt |- _ ] => rewrite -> Pos.compare_cont_refl in H; inversion H
  | [ H: _ (Pos.compare_cont Eq ?p ?p) = Gt |- _ ] => rewrite -> Pos.compare_cont_refl in H; inversion H
  | [ H: (Pos.compare_cont Eq ?p ?p) = Lt |- _ ] => rewrite -> Pos.compare_cont_refl in H; inversion H
  | [ H: (Pos.compare_cont Eq ?p ?p) = Gt |- _ ] => rewrite -> Pos.compare_cont_refl in H; inversion H
  end.