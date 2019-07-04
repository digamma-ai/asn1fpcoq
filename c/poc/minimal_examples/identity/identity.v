From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Local Open Scope Z_scope.

Definition _n : ident := 53%positive.

Definition f_identity := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _n tint)))
|}.

Definition identity_statement := f_identity.(fn_body).

Definition identity_fspec (n : Z) := n.

Section ID0.
  
  Let env0 : temp_env := Maps.PTree.set _n (Vint (Int.repr 0)) (Maps.PTree.empty val).

  Lemma f_identity0 (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
    exists (res_tr : trace) (res_te : temp_env),
      exec_stmt
      any_genv
      any_env
      env0
      any_mem
      identity_statement
      res_tr
      res_te
      any_mem
      (Out_return (Some ((Vint (Int.repr 0), tint)))).
  Proof.
    repeat eexists.
    repeat constructor.
  Qed.

End ID0.

Theorem f_identity_correct (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
  forall (tenv : temp_env) (n : Z),
    tenv!_n = Some (Vint (Int.repr n)) ->
    exists (res_tr : trace) (res_te : temp_env),
      exec_stmt
      any_genv
      any_env
      tenv
      any_mem
      identity_statement
      res_tr
      res_te
      any_mem
      (Out_return (Some ((Vint (Int.repr (identity_fspec n)), tint)))).
Proof.
  intros.
  repeat eexists.
  repeat constructor.
  assumption.
Qed.
