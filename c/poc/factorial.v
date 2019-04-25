From Coq Require Import String List ZArith Arith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Maps Values ClightBigstep Events.

Local Open Scope Z_scope.


Definition _input : ident := 53%positive.
Definition _output : ident := 54%positive.

Definition f_factorial := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_input, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_output, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _output (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Swhile
      (Etempvar _input tint)
      (Ssequence
        (Sset _output
          (Ebinop Omul (Etempvar _output tint) (Etempvar _input tint) tint))
        (Sset _input
          (Ebinop Osub (Etempvar _input tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _output tint)))))
|}.


Definition lempty := Maps.PTree.empty val.

Ltac exec_loop_continue := 
repeat match goal with
       | [ |- exec_stmt _ _ _ (Sloop _) _ _ _ _ ] => idtac
       | _ => econstructor ; exec_loop_continue
       end. 

(* runs on some inputs *)

Definition input1 := Maps.PTree.set _input (Vint (Int.repr 1)) lempty.
Proposition fact1 :
  forall ge e m, exists t le' out,  
      exec_stmt ge e input1 m f_factorial.(fn_body) t le' m  out /\ (le'!_output) = Some (Vint (Int.repr 1)).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sseq_1.
  econstructor. econstructor.
  eapply exec_Sseq_1.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_stop1.   (* stop the loop *)
  eapply exec_Sseq_2. exec_loop_continue. discriminate. repeat econstructor. repeat econstructor. repeat econstructor.
Qed.


Definition input2 := Maps.PTree.set _input (Vint (Int.repr 2)) lempty.

Proposition fact2 :
  forall ge e m, exists t le' out,  
                               exec_stmt ge e input2 m f_factorial.(fn_body) t le' m  out /\ (le'!_output) = Some (Vint (Int.repr 2)).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sseq_1.
  econstructor. econstructor.
  eapply exec_Sseq_1.
  
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_stop1.   (* stop the loop *)
  eapply exec_Sseq_2. exec_loop_continue. discriminate. progress econstructor. repeat econstructor. repeat econstructor.
Qed.

Definition input3 := Maps.PTree.set _input (Vint (Int.repr 3)) lempty.
Proposition fact3 :
  forall ge e m, exists t le' out,  
      exec_stmt ge e input3 m f_factorial.(fn_body) t le' m  out /\ (le'!_output) = Some (Vint (Int.repr 6)).
Proof.
Proof.
  intros.
  repeat eexists.
  eapply exec_Sseq_1.
  econstructor. econstructor.
  eapply exec_Sseq_1.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_stop1.   (* stop the loop *)
  eapply exec_Sseq_2. exec_loop_continue. discriminate. repeat econstructor. repeat econstructor. repeat econstructor.
Qed.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Definition factorial_loop := (Swhile
      (Etempvar _input tint)
      (Ssequence
        (Sset _output
          (Ebinop Omul (Etempvar _output tint) (Etempvar _input tint) tint))
        (Sset _input
          (Ebinop Osub (Etempvar _input tint) (Econst_int (Int.repr 1) tint)
                  tint)))).

(* Map from nat to values *)
Definition Vint_of_nat := fun n => Vint (Int.repr(Z_of_nat n)).

(* To prove things about ints go to Z via unsigned_repr_eq *)

Lemma zero_not_one_int : Int.zero <> Int.one.
  assert (Int.unsigned Int.one <> Int.unsigned Int.zero).
  { unfold Int.zero. rewrite Int.unsigned_repr_eq. rewrite Zmod_0_l. 
  rewrite Int.unsigned_one. congruence. } congruence.
  Qed.


Lemma succ_not_zero_int : forall n, Z.of_nat(S n) < Int.modulus -> Int.repr (Z.of_nat (S n)) <> Int.repr (Z.of_nat O).
Proof.
  intros. assert (Int.unsigned (Int.repr (Z.of_nat 0)) <> Int.unsigned (Int.repr (Z.of_nat (S n)))). simpl. rewrite Int.unsigned_repr_eq. rewrite Int.unsigned_repr_eq. rewrite  Zmod_0_l. rewrite Zmod_small. congruence. split. auto with zarith. apply H. congruence.
Qed.


Lemma Zpos_P_of_succ_Z_of_nat : forall n, Z.of_nat (S n) = Z.pos (Pos.of_succ_nat n).
Proof.
  intro. rewrite Zpos_P_of_succ_nat.  rewrite Nat2Z.inj_succ. reflexivity.
Qed.

Require Import Psatz.

Lemma fact_succ_geq : forall n, (S n <= fact (S n))%nat.
Proof.
  induction n.
  - auto.
  - simpl. simpl in IHn. rewrite <- Nat.add_1_r in *. rewrite <- Nat.add_1_r. lia.
  Qed.
  
Theorem factorial_loop_correct : forall ge e m, forall inp outp le,
      Z.of_nat inp < Int.modulus ->
      1 <= Z.of_nat outp < Int.modulus ->
      Z.of_nat ((fact inp)*outp) < Int.modulus -> 
      le!_input = Some (Vint_of_nat inp) ->
      le!_output = Some (Vint_of_nat outp) ->
      exists t le',
        exec_stmt ge e le m factorial_loop t le' m Out_normal
        /\ (le'!_output) = Some (Vint_of_nat ((fact inp)*outp)).
Proof.
  induction inp ; intros outp le H Hout Hloop H2 H3.
  (* Base case *)
  - repeat eexists.
    + eapply exec_Sloop_stop1. eapply exec_Sseq_2. repeat econstructor. apply H2. simpl.  econstructor. unfold Vint_of_nat. simpl. econstructor. discriminate. econstructor.
    + rewrite -> H3. simpl. unfold Vint_of_nat. rewrite Nat.add_0_r. reflexivity.
  (* Induction step *)
  - assert (exists (t : Events.trace) (le' : temp_env),
       exec_stmt ge e (Maps.PTree.set _input (Vint_of_nat inp) (Maps.PTree.set _output (Vint_of_nat (outp*S inp)) le)) m factorial_loop t le' m Out_normal /\
       le' ! _output =  Some (Vint_of_nat ((fact inp)*( outp * S inp)))).
    { apply IHinp.
      + apply Z.lt_succ_l. rewrite <- Nat2Z.inj_succ. apply H.   (* follows from H *)
      + pose (L := fact_succ_geq inp).
        nia.
      + simpl in Hloop. nia. 
      + apply PTree.gss.
      + rewrite PTree.gso. apply PTree.gss. cbv. congruence. } 
    + destruct H0. destruct H0. destruct H0. 
      repeat eexists.
      eapply exec_Sloop_loop. eapply exec_Sseq_1. repeat econstructor. apply H2. econstructor.
      cut (((Int.eq (Int.repr (Z.of_nat (S inp))) Int.zero)) = false). intro aux. rewrite aux. simpl.
      econstructor.
      { SearchAbout (Int.eq). rewrite <- (Int.eq_false (Int.repr (Z.of_nat (S inp))) Int.zero). auto. apply succ_not_zero_int. apply H. } 
        eapply exec_Sseq_1.
      repeat econstructor. apply H3. apply H2.
      repeat econstructor. repeat econstructor.
      cut ((PTree.set _output
                      (Vint
                         (Int.mul (cast_int_int I32 Signed (Int.repr (Z.of_nat outp)))
                                  (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp)))))) le)
             ! _input =  Some (Vint_of_nat (S inp))). intro aux.
      apply aux.
      { rewrite PTree.gso. apply H2. cbv. congruence. }
      repeat econstructor.
      econstructor.
      econstructor.
      cut (
          (PTree.set _input (Vint_of_nat inp)
                     (PTree.set _output (Vint_of_nat (outp * S inp)) le)) =
          (PTree.set _input
                     (Vint
                        (Int.sub (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp))))
                                 (cast_int_int I32 Signed (Int.repr 1))))
                     (PTree.set _output
                                (Vint
                                   (Int.mul (cast_int_int I32 Signed (Int.repr (Z.of_nat outp)))
                                            (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp))))))
                                le))
        ). intro aux.
      rewrite <- aux.
      apply H0.
      
      {    f_equal. unfold Vint_of_nat. f_equal.
         * simpl. unfold Int.sub. rewrite Int.unsigned_repr_eq. rewrite Int.unsigned_repr_eq. f_equal. repeat rewrite Zmod_small; nia.

         * f_equal. unfold Vint_of_nat. f_equal. simpl. unfold Int.mul. f_equal. rewrite Int.unsigned_repr_eq. rewrite Int.unsigned_repr_eq. repeat rewrite Zmod_small; nia. 
   
      }
       rewrite -> H1. simpl. f_equal. f_equal. ring.
Qed.

Theorem factorial_correct : forall ge e m n le,
    Z.of_nat n < Int.modulus ->
    Z.of_nat (fact n) < Int.modulus ->
    le!_input = Some (Vint_of_nat n) -> exists t le' out, exec_stmt ge e le m f_factorial.(fn_body) t le' m out /\ (le'!_output) = Some (Vint_of_nat (fact n)).
Proof.
  intros.
  assert (exists t le', exec_stmt ge e (PTree.set _output (Vint_of_nat 1) le) m factorial_loop t le' m Out_normal /\
             le' ! _output = Some (Vint_of_nat (fact n * 1))) .
  { eapply factorial_loop_correct.
    + apply H.
    + simpl. split; auto with zarith. pose Int.modulus_gt_one. nia. 
    + nia.      
    + rewrite PTree.gso. apply H1. cbv. congruence.
    + apply PTree.gss. }
   destruct H2. destruct H2.  destruct H2.
   eexists. eexists. exists (Out_return (Some (Vint_of_nat (fact n), tint))). split.
      + eapply exec_Sseq_1. econstructor. econstructor. eapply exec_Sseq_1. apply H2. repeat econstructor; rewrite Nat.mul_1_r in H3 ; exact H3.
      + rewrite Nat.mul_1_r in H3. exact H3.
 Qed.


(* Theorem factorial_loop_correct : forall ge e m, forall inp outp le,
      le!_input = Some (Vint_of_nat inp) ->
      le!_output = Some (Vint_of_nat outp) ->
      exists t le',
        exec_stmt ge e le m factorial_loop t le' m Out_normal
        /\ (le'!_output) = Some (Vint_of_nat ((fact inp)*outp)).
Proof.
  induction inp ; intros.
  (* Base case *)
  - repeat eexists.
    + eapply exec_Sloop_stop1. eapply exec_Sseq_2. repeat econstructor. apply H. simpl.  econstructor. unfold Vint_of_nat. simpl. econstructor. discriminate. econstructor.
    + rewrite -> H0. simpl. unfold Vint_of_nat. simpl. rewrite Nat.add_0_r. reflexivity.
  (* Induction step *)
  - assert (exists (t : Events.trace) (le' : temp_env),
       exec_stmt ge e (Maps.PTree.set _input (Vint_of_nat inp) (Maps.PTree.set _output (Vint_of_nat (outp*S inp)) le)) m factorial_loop t le' m Out_normal /\
       le' ! _output =  Some (Vint_of_nat ((fact inp)*( outp * S inp)))).
    { apply IHinp.
      + apply PTree.gss.
      + rewrite PTree.gso. apply PTree.gss. cbv. congruence. } 
    + destruct H1. destruct H1. destruct H1. 
      repeat eexists.
      eapply exec_Sloop_loop. eapply exec_Sseq_1. repeat econstructor. apply H. econstructor.
      cut (forall inp, ((Int.eq (Int.repr (Z.of_nat (S inp))) Int.zero)) = false). intro aux. rewrite aux. simpl.
      econstructor.
      { intro. SearchAbout (Int.eq). rewrite <- (Int.eq_false (Int.repr (Z.of_nat (S inp0))) Int.zero). auto. apply succ_not_zero_int. (* intrange assumption *) admit. } 
        eapply exec_Sseq_1.
      repeat econstructor. apply H0. apply H.
      repeat econstructor. repeat econstructor.
      cut ((PTree.set _output
                      (Vint
                         (Int.mul (cast_int_int I32 Signed (Int.repr (Z.of_nat outp)))
                                  (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp)))))) le)
             ! _input =  Some (Vint_of_nat (S inp))). intro aux.
      apply aux.
      { rewrite PTree.gso. apply H. cbv. congruence. }
      repeat econstructor.
      econstructor.
      econstructor.
      cut (
          (PTree.set _input (Vint_of_nat inp)
                     (PTree.set _output (Vint_of_nat (outp * S inp)) le)) =
          (PTree.set _input
                     (Vint
                        (Int.sub (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp))))
                                 (cast_int_int I32 Signed (Int.repr 1))))
                     (PTree.set _output
                                (Vint
                                   (Int.mul (cast_int_int I32 Signed (Int.repr (Z.of_nat outp)))
                                            (cast_int_int I32 Signed (Int.repr (Z.of_nat (S inp))))))
                                le))
        ). intro aux.
      rewrite <- aux.
      apply H1.
      (* done! *)
      { f_equal. simpl. admit. unfold Vint_of_nat. admit.  }   
       rewrite -> H2. simpl. f_equal. f_equal. ring.
Admitted.
 *)      
