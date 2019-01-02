Require Import Coq.PArith.BinPos.
Require Import Coq.PArith.Pnat.
Require Import Coq.Arith.Wf_nat.

(* Strong induction on `positive` numbers *)

Open Scope positive_scope.

Let Plt_wf : well_founded Pos.lt.
Proof.
  apply well_founded_lt_compat with Pos.to_nat.
  intros x y H. apply Pos2Nat.inj_lt, H.
Qed.

Definition positive_lt_rec := well_founded_induction_type Plt_wf.

Definition positive_lt_ind := well_founded_induction Plt_wf.
