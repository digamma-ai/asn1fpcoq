From Coq Require Import String List ZArith Arith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Maps Values ClightBigstep Events.

Local Open Scope Z_scope.

(* Output of C light generator on factorial.c: *)

(* We have to variables input and output represented as positive numbers *)
Definition _input : ident := 53%positive.
Definition _output : ident := 54%positive.

Definition f_factorial := {|
  fn_return := tint; (* the return type is integer *)
  fn_callconv := cc_default; (* ignore this: relevant for small-step semantics *)
  fn_params := ((_input, tint) :: nil); (* input variable is the parameter of the function *)
  fn_vars := nil; 
  fn_temps := ((_output, tint) :: nil); (* output is a local variable *)
  fn_body := (* C light statement corresponding to the function *)
(Ssequence
  (Sset _output (Econst_int (Int.repr 1) tint)) (* int output = 1 *)
  (Ssequence 
    (Swhile 
      (Etempvar _input tint) (* while (input) *)
      (Ssequence  
        (Sset _output
          (Ebinop Omul (Etempvar _output tint) (Etempvar _input tint) tint)) (* output = output*input *)
        (Sset _input
          (Ebinop Osub (Etempvar _input tint) (Econst_int (Int.repr 1) tint) (* input = input - 1 *)
            tint))))
    (Sreturn (Some (Etempvar _output tint))))) (* return output *)
|}.

(* Now we can evaluate the statement of the function fn_body using the big-step semantics relation exec_stmt *)

(* We start in an empty environment *)
Definition lempty := Maps.PTree.empty val.

(* And map _input to integer value 1 *)
Definition input_1 := Maps.PTree.set _input (Vint (Int.repr 1)) lempty.

(* Then we can show that for any global and local environments and memory (these are irrelevant here), if input is mapped to 1, then the factorial statement evaluates to some environment in which output is mapped to 1 and outcome return 1 *)
(* Basically we are running a test of factorial on input 1 *)
Proposition fact1 :
  forall ge e m, exists t le',  
      exec_stmt ge e input_1 m f_factorial.(fn_body) t le' m (Out_return (Some  ((Vint (Int.repr 1), tint))))  /\ (le'!_output) = Some (Vint (Int.repr 1)).
Proof.
   intros.
   repeat eexists.
   (* unfold (fn_body f_factorial) *)
   simpl.
   (* search for a suitable constructor. we have a sequence of set and a while loop. set always has Out_normal as an outcome, so we need to apply exec_Sseq_1 *)
   eapply exec_Sseq_1.
    (* evaluate the set expression *)
   eapply exec_Sset.
   (* evaluate constant expression *)
   eapply eval_Econst_int. (* we reached an axiom and evaluated _output to Value 1 *)
   (* Now we have sequence of while and return. we want to execute one loop of the function with the normal outcome before the break *)
   eapply exec_Sseq_1.
   (* while is syntactic sugar for loop with an if then else condition *)
   eapply exec_Sloop_loop.
   eapply exec_Sseq_1.
   (* Evaluating if then else statement *)
   eapply exec_Sifthenelse.
   (* Temp variable is evaluated according to the local environment input_1 *)
   eapply eval_Etempvar.
   simpl.
   f_equal.
   (* evaluate boolean condition *)
   econstructor.
   assert (negb (Int.eq (Int.repr 1) Int.zero) = true) by (auto with ints). (* ints are hints to work on CompCert's ineger type *)
   rewrite H.
   (* Now we reached an axiom about Skip statement *)
   eapply exec_Sskip.
   (* Set input and output variables to the new values *)
   eapply exec_Sseq_1.
   eapply exec_Sset.
   (* evaluate multiplication expression input*output *)
   eapply eval_Ebinop.
   eapply eval_Etempvar.
   simpl.
   f_equal.
   eapply eval_Etempvar.
   simpl.
   f_equal.
   simpl.
   econstructor.
   (* evaluate substraction expression input - 1 *)
   repeat econstructor. (* replace this by concrete steps *)
   (* Axiom *) econstructor.
   (* Axiom *) eapply exec_Sskip.
   (* now break from the loop and return the output *)
   eapply exec_Sloop_stop1.   (* stop the loop *)
   (* The outcome of the loop is break so we choose a different sequence constructor *)
   eapply exec_Sseq_2.
   (* Here everything can be solved by econstructor *)
    repeat econstructor. discriminate. all: repeat econstructor. 
Qed.


(* Now we do the same for input = 2 *)
Definition input2 := Maps.PTree.set _input (Vint (Int.repr 2)) lempty.

(* We need to choose which loop constructor to apply, but in-between it is deterministic and we can use econstructor *)

Ltac exec_loop_continue := 
     repeat match goal with
            | [ |- exec_stmt _ _ _ (Sloop _) _ _ _ _ ] => idtac
            | _ => econstructor ; exec_loop_continue
            end. 
   
Proposition fact2 :
  forall ge e m, exists t le' out,  
                               exec_stmt ge e input2 m f_factorial.(fn_body) t le' m  out /\ (le'!_output) = Some (Vint (Int.repr 2)).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sseq_1.
  repeat econstructor.
  econstructor.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_loop. exec_loop_continue. econstructor. econstructor.
  eapply exec_Sloop_stop1.   (* stop the loop *)
  eapply exec_Sseq_2.  exec_loop_continue. discriminate. progress econstructor. repeat econstructor. repeat econstructor.
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

Inductive factorial : nat -> nat -> Prop :=
| FactZero : factorial 0 1
| FactSucc : forall n m, factorial n m -> factorial (S n) ((S n)*m).                      

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
    + eapply exec_Sloop_stop1. eapply exec_Sseq_2. repeat econstructor. apply H2.  econstructor.  econstructor. discriminate. econstructor.
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
    destruct H0. destruct H0. destruct H0. 
    repeat eexists.
    + eapply exec_Sloop_loop.
      eapply exec_Sseq_1. repeat econstructor. apply H2. econstructor.
      rewrite -> (Int.eq_false (Int.repr (Z.of_nat (S inp))) Int.zero). econstructor. apply succ_not_zero_int. apply H.
      eapply exec_Sseq_1.
      repeat econstructor. apply H3. apply H2.
      repeat econstructor. repeat econstructor.
      rewrite PTree.gso. apply H2.  cbv. congruence.
      repeat econstructor.
      econstructor.
      econstructor.
      assert ((PTree.set _input (Vint_of_nat inp)
                     (PTree.set _output (Vint_of_nat (outp * S inp)) le)) = (PTree.set _input (Vint (Int.sub (Int.repr (Z.of_nat (S inp))) (Int.repr 1))) (PTree.set _output (Vint (Int.mul (Int.repr (Z.of_nat outp)) (Int.repr (Z.of_nat (S inp))))) le))).
      {    unfold Vint_of_nat. repeat f_equal.
           unfold Int.sub. repeat rewrite Int.unsigned_repr_eq. f_equal. repeat rewrite Zmod_small; nia.
           unfold Int.mul. f_equal. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Zmod_small; nia.
           }
        rewrite <- H4. eapply H0.
        + rewrite -> H1. simpl. f_equal. f_equal. nia.
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
    + simpl. split; auto with zarith. cbv. auto. 
    + nia.      
    + rewrite PTree.gso. apply H1. cbv. congruence.
    + apply PTree.gss. }
   destruct H2. destruct H2.  destruct H2.
   eexists. eexists. exists (Out_return (Some (Vint_of_nat (fact n), tint))). split.
      + eapply exec_Sseq_1. econstructor. econstructor. eapply exec_Sseq_1. apply H2. repeat econstructor; rewrite Nat.mul_1_r in H3 ; exact H3.
      + rewrite Nat.mul_1_r in H3. exact H3.
 Qed.
