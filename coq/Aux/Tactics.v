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

Ltac split_andb :=
  match goal with
    | [H : andb ?P1 ?P2 = true |- _ ] => apply andb_prop in H; inversion H; clear H
  end.

Ltac split_andb_goal :=
  match goal with
  | [ H : _ |- andb ?P ?Q = true] => repeat rewrite Bool.andb_true_iff; repeat split
  end.

(*
 *  different cases for
 *  (a ?= a) != Eq
 *)
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

Require Import Flocq.Core.Zaux.

Ltac debool :=
  repeat match goal with
         | [ H: Z.compare _ _ = Eq |- _ ] => apply Z.compare_eq in H

         | [ |- Zeq_bool _ _ = true ] => apply Zeq_bool_true
         | [ H: Zeq_bool _ _ = true |- _ ] => apply Zeq_bool_eq in H

         | [ |- (_ =? _)%nat = true ] => apply Nat.eqb_eq
         | [ H: (_ =? _)%nat = true |- _ ] => apply Nat.eqb_eq in H
         | [ |- (_ =? _)%nat = false ] => apply Nat.eqb_neq
         | [ H: (_ =? _)%nat = false |- _ ] => apply Nat.eqb_neq in H

         | [ |- (_ <? _)%Z = true ] => apply Zlt_bool_true
         | [ H: (_ <? _)%Z = true |- _ ] => apply Z.ltb_lt in H
         | [ |- (_ <? _)%Z = false ] => apply Zlt_bool_false
         | [ H: (_ <? _)%Z = false |- _ ] => apply Z.ltb_ge in H

         | [ |- (_ =? _)%Z = true ] => apply Z.eqb_eq
         | [ H: (_ =? _)%Z = true |- _ ] => apply Z.eqb_eq in H
         | [ |- (_ =? _)%Z = false ] => apply Z.eqb_neq
         | [ H: (_ =? _)%Z = false |- _ ] => apply Z.eqb_neq in H

         | [ H: Bool.eqb _ _ = true |- _ ] => apply Bool.eqb_prop in H

         | [ |- Z.leb _ _ = true ] => apply Zle_bool_true
         | [ H: Z.leb _ _ = true |- _] => apply Zle_bool_imp_le in H

         | [ H: Z.compare _ _ = Gt |- _ ] => apply Z.compare_gt_iff in H
         | [ H: Z.compare _ _ = Lt |- _ ] => rewrite Z.compare_lt_iff in H
         end.