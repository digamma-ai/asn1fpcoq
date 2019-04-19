From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Maps Values ClightBigstep.
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

Definition Vint_of_nat := fun n => Vint (Int.repr(Z_of_nat n)).

Theorem factorial_loop_correct : forall ge e m, forall inp outp le,
      le!_input = Some (Vint_of_nat inp) ->
      le!_output = Some (Vint_of_nat outp) ->
      exists t le' out,
        exec_stmt ge e le m factorial_loop t le' m out
        /\ (le'!_output) = Some (Vint_of_nat ((fact inp)*outp)).
Proof.
  induction inp.
  - intros. repeat eexists. eapply exec_Sloop_stop1. eapply exec_Sseq_2.    repeat econstructor. apply H. simpl.  econstructor. unfold Vint_of_nat. simpl. econstructor. discriminate. econstructor. rewrite -> H0. simpl. unfold Vint_of_nat. simpl. rewrite Nat.add_0_r. reflexivity. 
  - intros.  repeat eexists.
    +  assert (exists (t : Events.trace) (le' : temp_env) (out : outcome),
       exec_stmt ge e (Maps.PTree.set _input (Vint_of_nat inp) (Maps.PTree.set _output (Vint_of_nat (outp*S inp)) le)) m factorial_loop t le' m out /\
       le' ! _output = 
       Some (Vint_of_nat ((fact inp)*( outp * S inp)))).
       apply IHinp. apply PTree.gss.  admit. (*true : set-get lemma*)
       eapply exec_Sloop_stop1.  eapply exec_Sseq_2. econstructor. econstructor. apply H. econstructor.
       Admitted.
         
  

Theorem factorial_correct : forall ge e m n le, le!_input = Some (Vint_of_nat n) ->
                                                        exists t le' out,
                                                          exec_stmt ge e le m f_factorial.(fn_body) t le' m  out
                                                          /\ (le'!_output) = Some (Vint_of_nat (fact n)).
Admitted.


(* runs on some inputs *)
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
