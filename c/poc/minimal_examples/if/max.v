From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Local Open Scope Z_scope.

Definition _res : ident := 55%positive.
Definition _s1 : ident := 53%positive.
Definition _s2 : ident := 54%positive.

Definition f_max := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s1, tint) :: (_s2, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ogt (Etempvar _s1 tint) (Etempvar _s2 tint) tint)
    (Sset _res (Etempvar _s1 tint))
    (Sset _res (Etempvar _s2 tint)))
  (Sreturn (Some (Etempvar _res tint))))
|}.

Theorem f_max_correct (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
  forall (tenv : temp_env) (s1 s2 : Z),
    tenv!_s1 = Some (Vint (Int.repr s1)) ->
    tenv!_s2 = Some (Vint (Int.repr s2)) ->
    Int.min_signed <= s1 <= Int.max_signed ->
    Int.min_signed <= s2 <= Int.max_signed ->
    exists (res_tr : trace) (res_te : temp_env),
      exec_stmt
        any_genv
        any_env
        tenv
        any_mem
        f_max.(fn_body)
        res_tr
        res_te
        any_mem
        (Out_return (Some ((Vint (Int.repr (Z.max s1 s2)), tint)))).
Admitted.
