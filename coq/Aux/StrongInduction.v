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

Lemma positive_lt_rec :
  forall P:positive -> Type,
    (forall x:positive, (forall y:positive, y < x -> P y) -> P x) ->
    forall x:positive, P x.
Proof.
  intros P Hrec.
  induction x as [x IH] using (well_founded_induction_type Plt_wf).
  destruct x; apply Hrec; trivial.
Defined.

Lemma positive_lt_ind :
  forall P:positive -> Prop,
    (forall x:positive, (forall y:positive, y < x -> P y) -> P x) ->
    forall x:positive, P x.
Proof. intros; now apply positive_lt_rec. Qed.
