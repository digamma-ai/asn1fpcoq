From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From compcert Require Import Maps Values ClightBigstep Events.

Local Open Scope Z_scope. Definition _s1 : ident := 53%positive.
Definition _s2 : ident := 54%positive.

Definition f_sum := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s1, tint) :: (_s2, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _s1 tint) (Etempvar _s2 tint) tint)))
|}.

Definition sum_statement := f_sum.(fn_body).

Definition sum_fspec (s1 s2 : Z) := s1 + s2.

Theorem f_sum_correct (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
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
        sum_statement
        res_tr
        res_te
        any_mem
        (Out_return (Some ((Vint (Int.repr (sum_fspec s1 s2)), tint)))).
Proof.
  intros.
  repeat eexists.
  repeat econstructor.
  - apply H.
  - apply H0.
  - cbn.
    unfold sem_binarith; simpl.
    repeat rewrite cast_val_casted by (econstructor; auto).
    repeat rewrite Int.add_signed.
    repeat rewrite Int.signed_repr.
    reflexivity.
    assumption.
    assumption.
Qed.

Definition sum_fspec_int (s1 s2 : int) := Int.add s1 s2.

Theorem f_sum_correct_int (any_genv : genv) (any_env : env) (any_mem : Memory.Mem.mem) :
  forall (tenv : temp_env) (s1 s2 : int),
    tenv!_s1 = Some (Vint s1) ->
    tenv!_s2 = Some (Vint s2) ->
    exists (res_tr : trace) (res_te : temp_env),
      exec_stmt
        any_genv
        any_env
        tenv
        any_mem
        sum_statement
        res_tr
        res_te
        any_mem
        (Out_return (Some (Vint (sum_fspec_int s1 s2), tint))).
Proof.
  intros.
  repeat eexists.
  repeat econstructor.
  - apply H.
  - apply H0.
  - unfold sum_fspec_int.
    econstructor.
Qed.

Proposition sum_fspec_refine_r: forall s1 s2 s3, sum_fspec s1 s2 = s3 -> sum_fspec_int (Int.repr s1) (Int.repr s2) = Int.repr s3.
Proof.
  unfold sum_fspec.
  unfold sum_fspec_int.
  intros.  
  rewrite <- H.
  unfold Int.add.
  repeat rewrite Int.unsigned_repr_eq.
  assert ((s1 + s2) mod Int.modulus = (s1 mod Int.modulus + s2 mod Int.modulus) mod Int.modulus) by (eapply Zplus_mod).
  (* there should be a lemma like this somewhere in CompCert... *)
  assert  (Int.repr (s1 + s2) = Int.mkint (Int.Z_mod_modulus (s1 + s2)) (Int.Z_mod_modulus_range' (s1 + s2))) by (auto with ints).
  rewrite H1.
  assert (Int.repr (s1 mod Int.modulus + s2 mod Int.modulus) =
          Int.mkint (Int.Z_mod_modulus (s1 mod Int.modulus +  s2 mod Int.modulus)) (Int.Z_mod_modulus_range' (s1 mod Int.modulus +  s2 mod Int.modulus))) by (auto with ints). 
  rewrite H2.
  apply Int.mkint_eq.
  repeat rewrite Int.Z_mod_modulus_eq.
  nia.
Qed.


(* The opposite direction needs preconditions *)
Proposition sum_fspec_refine_l: forall s1 s2 s3,
    Int.min_signed <= s1 <= Int.max_signed ->
    Int.min_signed <= s2 <= Int.max_signed ->
    Int.min_signed <= s3 <= Int.max_signed ->
    sum_fspec_int (Int.repr s1) (Int.repr s2) = Int.repr s3 ->
                                            sum_fspec s1 s2 = s3.
Proof.
  Admitted.
