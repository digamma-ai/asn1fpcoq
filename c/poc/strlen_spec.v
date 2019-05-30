(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
(* Local Open Scope Z_scope.*)

(* Some useful notation and tactics *)

Definition chunk : memory_chunk := Mint8unsigned.
Definition VintZ := fun (z : Z) => Vint (Int.repr z).
Definition VintN:= fun n => Vint (Int.repr(Z_of_nat n)).
Definition VintP := fun p : positive => Vint (Int.repr (Z.pos p)).

Notation gso := PTree.gso.
Notation gss := PTree.gss.

(* Tactics for arithmetic on ptrofs, now they are ad hoc, TODO: automatize translation from ptrofs to Z *)

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_compute_add_mul :=
      simpl; unfold Ptrofs.add; unfold Ptrofs.mul; unfold Ptrofs.of_intu; unfold Ptrofs.of_int;
      repeat rewrite Ptrofs.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ints_compute_add_mul :=
      simpl; unfold Int.add; unfold Int.mul;
      repeat rewrite Int.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.
Ltac gss := eapply gss.

Ltac gso_assumption :=
  match goal with
  | [ H : ?P ! ?I = Some ?W |- (PTree.set _ _ ?P) ! ?I = Some ?Z ] => rewrite gso  
  | [ H : ?P ! ?Q = Some ?W |-  ?P ! ?Q = Some ?Z ] => apply H
  | [ |- _ <> _ ] => cbv ; congruence
  end.

 Ltac invert_clear :=
        match goal with
          | [H : context[exec_stmt] |- _] =>
            inversion_clear H 
          | [H : context[eval_expr] |- _] =>
            inversion_clear H 
          | [H : context[eval_lvalue] |- _] =>
            inversion_clear H 
          | [H : context[bool_val] |- _] =>
            inversion_clear H  
          | [H : context[deref_loc] |- _] =>
            inversion_clear H  
          | [H : context[sem_binary_operation] |- _] =>
           inversion_clear H  
          | [H : context[access_mode] |- _] =>
            inversion_clear H
          | [H : context[ out_break_or_return] |- _] => inversion_clear H                  
          | _ => idtac
        end.    


Ltac solve_by_inverts n :=
   match n with
   | O => idtac
   | S (?n') => invert_clear ; solve_by_inverts n'
end.

(* Recursive specification of strlen function *)

(* unsigned C char *)
Definition C_uchar : Set := positive.

 (* C string *) 
Inductive C_string : Set :=
| CEmptyString : C_string
| CString : positive -> C_string -> C_string.

Inductive strlen : C_string -> nat -> Prop :=
| LengthZero : strlen CEmptyString 0
| LengthSucc : forall n s c, strlen s n -> strlen (CString c s) (S n).

Inductive strlen_mem_op : mem -> block -> Z -> option (C_string*nat) -> Prop :=
| LengthZeroMem_op : forall m b ofs, Mem.load Mint8signed m b ofs = Some (VintZ 0) -> strlen_mem_op m b ofs (Some (CEmptyString, O))
| LengthSuccMem_op : forall m b ofs c s n, strlen_mem_op m b (ofs + 1) (Some (s,n)) -> Mem.load Mint8signed m b ofs = Some (VintP c) -> strlen_mem_op m b ofs (Some ((CString c s),(S n))).

Inductive strlen_mem : mem -> block -> Z -> nat -> Prop :=
| LengthZeroMem m b ofs: Mem.load Mint8unsigned m b ofs = Some (VintZ 0) -> strlen_mem m b ofs 0
| LengthSuccMem m b ofs: forall p v,
    strlen_mem m b (ofs+1) p ->
    Mem.load Mint8unsigned m b ofs = Some (VintP v) ->
    strlen_mem m b ofs (S p).


(* Try induction on strlen type *)

(* strlen C light AST *)

Definition _output : ident := 4%positive.
Definition _input : ident := 3%positive.
Definition _t'1 : ident := 7%positive.
Definition _t'2 : ident := 8%positive.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_input, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_output, tuint) :: (_t'1, (tptr tuchar)) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _output (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tuchar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
            (Sifthenelse (Etempvar _t'2 tuchar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _output tuint)))))
                          |}.

Definition f_strlen_loop :=
  (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tuchar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
            (Sifthenelse (Etempvar _t'2 tuchar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip).

Print Sloop.

Definition f_strlen_loop_body := (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _input (tptr tuchar)))
            (Sset _input
              (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
          (Ssequence
            (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
            (Sifthenelse (Etempvar _t'2 tuchar) Sskip Sbreak)))
        (Sset _output
          (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
            tuint))).

(* Correctness statements *)
(* On empty string C light function evaluates to 0 *)

Lemma strlen_correct_loop_empty_string :
  (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->                      
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintN O) ->                     
    (* Precondition: reading empty C string from memory *)
    strlen_mem m b ofs O ->
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN O).
Proof.
  intros.
  inversion_clear H5.
  repeat eexists.
  eapply exec_Sloop_stop1.
  seq2. repeat econstructor. gso_assumption. apply gss.
  repeat econstructor. rewrite gso. apply gss. cbv; congruence. simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr ofs)) with ofs. 
  apply H6.
  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
  apply gss. econstructor.
  replace (negb (Int.eq (Int.repr 0) Int.zero)) with false by simpl.
  econstructor.
  cbv; congruence.
  econstructor.
  repeat (rewrite gso). assumption. all: cbv; congruence.
Qed.


(* Test case: On a string of length 2 C light function evaluates to 0 *)
Lemma strlen_correct_test :
  (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->                      
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->                     
    (* Precondition: reading  C string of length 2 from memory *)
    strlen_mem m b ofs 2%nat ->
    
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintZ 2),tuint))) /\ (le'!_output) = Some (VintZ 2).
Proof.
  intros.
  inversion_clear H5. inversion_clear H6. inversion_clear H5.
  repeat eexists.
  - seq1.
    -- sset. (* evaluate expression *) repeat econstructor.
    -- seq1.   
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss. repeat econstructor.
        rewrite gso. apply gss. cbv. congruence. simpl. ptrofs_to_Z. apply H7. assumption.
        apply gss.
        simpl.
        econstructor.
        replace (negb (Int.eq (Int.repr (Z.pos v)) Int.zero)) with true by admit.      
        econstructor.
        repeat econstructor. repeat econstructor. repeat econstructor.
        rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv ;congruence.
        repeat econstructor. econstructor. econstructor.

        (* loop 2 *)
        loop. repeat econstructor. repeat gso_assumption.
        rewrite gso. rewrite gso. apply gss. 1-2: cbv ; congruence.
        apply gss.
        repeat econstructor.
        rewrite gso. apply gss. cbv ; congruence.
        simpl.
        replace (Ptrofs.unsigned
                   (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))))) with (ofs + 1) by admit.
        apply H8.        
        apply gss.
        simpl.
        econstructor.
        replace (negb (Int.eq (Int.repr (Z.pos v0)) Int.zero)) with true by admit.      
        econstructor.
        rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv ; congruence.
        repeat econstructor. econstructor. econstructor.
            
         (* exit loop *)
        eapply exec_Sloop_stop1.
        seq2. seq1. seq1. econstructor. econstructor. rewrite gso. rewrite gso. apply gss. 1-2: cbv ; congruence.
        repeat econstructor.
        apply gss.
        repeat econstructor.
        seq1. repeat econstructor.
        rewrite gso. apply gss. cbv ; congruence.
        simpl.
      
        replace (Ptrofs.unsigned
       (Ptrofs.add
          (Ptrofs.add (Ptrofs.repr ofs)
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))))
          (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))))) with (ofs + 1 + 1) by admit.        apply H6.
        repeat econstructor.
        apply gss.
        simpl.
        econstructor. 
        replace (negb (Int.eq (Int.repr 0) Int.zero)) with false by (simpl).
        econstructor.
        cbv; congruence.
        econstructor.
      * (* return statement *)
        repeat econstructor.  rewrite gso.  rewrite gso.  rewrite gso.  eapply gss. all: cbv; congruence.
  - rewrite gso.  rewrite gso.  rewrite gso.  eapply gss. all: cbv ; congruence.
Admitted.

(* Conditions about the f_strlen loop *)
(* If 0 is read from memory at [b,ofs + len] the output is set to len *)
Lemma strlen_loop_break_correct : Archi.ptr64 = false -> forall ge e m b ofs outp le,
      
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 <= ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->

      (* IF before the loop *s = [b,ofs + outp] and i = outp *)
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat outp))) ->
      le!_output = Some (VintN outp) ->
      
      (* and the guard condition is false *)
      Mem.load Mint8unsigned m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->

      (* THEN loop executes to an environment with i = outp [i.e., i stays unchanged] + memory is unchanged *)
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ (le'!_output) = Some (VintN outp).
Proof.
  intros.
  repeat eexists.
  eapply exec_Sloop_stop1.
  seq2. seq1. seq1.
  repeat econstructor.
  apply H3.
  repeat econstructor.
  apply gss.
  repeat econstructor.
  seq1.
  repeat econstructor.
  rewrite gso. apply gss. cbv ; congruence.
  unfold Mem.loadv.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat outp))) with (ofs + Z.of_nat outp) by admit.
  apply H5.
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq (Int.repr 0) Int.zero)) with false by (simpl).
  econstructor.
  cbv; congruence.
  econstructor.
  repeat (rewrite gso). assumption.
  all: cbv; congruence.
Admitted.

Print exec_stmt.

(* Helper lemmas about strlen_mem *)

Lemma strlen_trans_len_0 : forall len m b ofs, strlen_mem m b ofs len -> strlen_mem m b (ofs + Z.of_nat len) O.
Proof.
  induction len ; intros.
  - replace (ofs + Z.of_nat 0) with ofs by nia. assumption.
  - inversion_clear H.
    replace (ofs + Z.of_nat (S len)) with (ofs + 1 + Z.of_nat len) by nia.
    apply (IHlen m b (ofs + 1) H0).
Qed.

Lemma strlen_trans_len_i : forall len m b ofs, strlen_mem m b ofs len -> forall i, (i < len)%nat -> strlen_mem m b (ofs + Z.of_nat i) (len - i)%nat.
Proof.
  induction len.
  - intros. omega.
  - induction i ; intro.
    + replace (ofs + Z.of_nat 0) with ofs by nia.
       replace  (S len - 0)%nat with (S len)%nat by omega. assumption. 
    + inversion_clear H.
       assert (i < len)%nat by omega. pose (IHlen m b (ofs + 1) H1 i H).
       replace (S len - S i)%nat with (len - i)%nat by omega.
       replace (ofs + Z.of_nat (S i)) with  (ofs + 1 + Z.of_nat i) by nia.
       assumption.
Qed.  
   
Lemma strlen_to_mem : forall len m b ofs, strlen_mem m b ofs len ->
                                     forall i, (i < len)%nat -> exists p : positive, Mem.load chunk m b (ofs + Z.of_nat i) = Some (VintP p).
Proof.
  induction len.
  - intros. omega.
  -  induction i ; intro ; inversion_clear H.
    +  replace (ofs + Z.of_nat 0) with ofs by nia.
       exists v. assumption.
    +  assert (i < len)%nat by omega. pose (IHlen m b (ofs + 1) H1 i H).
       replace (ofs + Z.of_nat (S i)) with  (ofs + 1 + Z.of_nat i) by nia.
       assumption.  
Qed.

Lemma strlen_loop_body_correct: Archi.ptr64 = false -> forall len ge e m b ofs le,
      0 <= ofs < Ptrofs.modulus ->
      Z_of_nat len < Int.modulus ->
      ofs + Z_of_nat len < Ptrofs.modulus ->
                       
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) ->
      le!_output = Some (VintN len) ->
    
      (exists p, Mem.load chunk m b (ofs + Z.of_nat len) = Some (VintP p)) ->
                                         
      exists t le', exec_stmt ge e le m f_strlen_loop_body t le' m Out_normal /\ le'!_output = Some (VintN (S len)).
Proof.
  intros.
  destruct H5 as [p].
  repeat eexists.
  repeat seq1.
  repeat econstructor. apply H3. repeat econstructor.
  apply gss.
  repeat econstructor.
  repeat econstructor.
  rewrite gso. apply gss. cbv; congruence.
  simpl.
  replace (Ptrofs.unsigned (Ptrofs.repr (ofs + Z.of_nat len))) with (ofs + Z.of_nat len) by admit.
  apply H5.
  repeat econstructor.
  apply gss.
  econstructor.
  replace (negb (Int.eq (Int.repr (Z.pos p)) Int.zero)) with true by admit.
  repeat econstructor.
  repeat econstructor.
  repeat (rewrite gso).
  apply H4. 1-3: cbv; congruence.
  repeat econstructor.
  unfold VintN.
  replace (Int.add (Int.repr (Z.of_nat len)) (Int.repr 1)) with (Int.repr (Z.of_nat (S len))) by admit.
  apply gss.
Admitted.


Lemma exec_succ_output : forall ge e le m b ofs n,
    (exists t1 le1, exec_stmt ge e (PTree.set _output (VintZ 0) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m f_strlen_loop t1  (PTree.set _output (VintN n) le1) m Out_normal) ->

    exists t2 le2, exec_stmt ge e (PTree.set _output (VintZ 1) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m f_strlen_loop t2 (PTree.set _output (VintN (S n)) le2) m Out_normal.
Admitted.

Lemma exec_succ_output_gen : forall ge e le m b ofs i n,
    
    (exists t1 le1, exec_stmt ge e (PTree.set _output (VintN i) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) le)) m f_strlen_loop t1 (PTree.set _output (VintN n) le1) m Out_normal) ->


    (exists t2 le2, exec_stmt ge e  (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le) m f_strlen_loop t2
       (PTree.set _output (VintN (n + i)%nat) (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le2)) m
       Out_normal).
  Admitted.


Lemma strlen_loop_correct_gen_new : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false -> (* TODO: remove this assumption *)
  forall len i ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *) 0 <= ofs < Ptrofs.modulus ->
    0 <= ofs + Z_of_nat len + Z_of_nat i < Ptrofs.modulus ->   
       (* Precondition: reading C string of length len from memory *)
    strlen_mem m b ofs (len + i) ->
              
    exists t le',
      le!_output = Some (VintN i) ->
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) ->
      exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (len + i)).
Proof.
  induction len; intros until le; intros Bound1 Bound2 Spec; pose (Ptrofs.modulus_eq32 H).
  - (* Base case *)    
    simpl in Spec.
    repeat eexists.
    (* Exit the loop *)
    eapply exec_Sloop_stop1. seq2. repeat econstructor.
    apply H1.
    eapply gss.
    repeat econstructor.
    rewrite gso. apply gss. cbv. congruence.
    (* Derive memory assumptions from the specification *)
    pose (Spec_mem := strlen_trans_len_0 i m b ofs Spec).
    inversion_clear Spec_mem.
    simpl. 
    ptrofs_to_Z. apply H2.
    lia.
    apply gss.
    simpl.
    econstructor.
    replace (negb (Int.eq (Int.repr 0) Int.zero)) with false by simpl.      
    econstructor.
    cbv; congruence. econstructor.
    repeat (rewrite gso).
    replace (0 + i)%nat with i by lia.
    assumption.
    1-3: cbv; congruence.
  - (* Ind. Step *)
    assert (exists char, Mem.load Mint8unsigned m b (ofs + Z.of_nat i) = Some (VintP char)) as Mem. (* maybe not positive char ? *)
    { refine (strlen_to_mem (S len + i) m b ofs Spec i _). omega. }
    destruct Mem as [char Mem].
    (* apply I.H. to le' after one step when starting with i and [b,ofs + i]  *)
    pose (le'' :=  (PTree.set _output (VintN (S i))
       (PTree.set _t'2 (VintP char) (PTree.set _input
               (Vptr b (Ptrofs.repr (ofs + Z.of_nat (S i))))
          (PTree.set _t'1
                (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                      le))))).
    pose (IH := IHlen (S i) ge e m b ofs le'').
    assert ( exists (t : trace) (le' : temp_env),
       le'' ! _output = Some (VintN (S i)) -> 
       le''! _input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat (S i)))) ->               
       exec_stmt ge e le'' m f_strlen_loop t le' m
         Out_normal /\
       le' ! _output = Some (VintN (len + S i))) as Step.
    { eapply IH.
      1-2: lia.
      replace (len + S i)%nat with (S len + i)%nat by omega.
      assumption. }
    destruct Step as [s Step]. destruct Step as [t Step].
    (* Do one loop on the goal: then apply IH *)
    repeat eexists.
    loop. repeat econstructor.
    apply H1.
    eapply gss. 
    repeat econstructor.
    rewrite gso. apply gss. cbv; congruence.
    simpl. ptrofs_to_Z.
    apply Mem.
    lia.
    apply gss.
    econstructor.
    replace (negb (Int.eq (Int.repr (Z.pos char)) Int.zero)) with true. (* add lemma or revisit pos p : maybe just non-zero integer: use dependent type *)
    econstructor.
  {
    assert ((Int.eq (Int.repr (Z.pos char)) Int.zero = false)).
    rewrite Int.eq_false.
    reflexivity.
    unfold Int.zero.
    assert (0 <> Z.pos char) by lia.
    pose (Int.eqm_samerepr (Z.pos char) 0).
    unfold not.
    intro.
    pose (Int.eqm_small_eq (Z.pos char) 0).
    SearchAbout Int.zero.
    
    admit. admit. } 
  repeat (rewrite gso). apply H0. 1-3: cbv; congruence.
  repeat econstructor. econstructor. econstructor.
  fold f_strlen_loop.
  replace  (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)))
       (PTree.set _t'2 (VintP char)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat i))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tuchar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
             
                      le)))) with le''.
  eapply Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.

  { unfold le''.
    replace (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1))) with (VintN (S i)).
    replace (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat i))
                (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
                            (ptrofs_of_int Signed (Int.repr 1)))) with
        (Ptrofs.repr (ofs + Z.of_nat (S i))).
    reflexivity.
    simpl.
    unfold Ptrofs.of_ints.
    replace (Int.signed (Int.repr 1)) with 1 by (auto with ints).
    ptrofs_compute_add_mul.
    f_equal.
    1-5: lia.
    unfold VintN.
    f_equal.
    ints_compute_add_mul.
    f_equal.
    1-3: lia. }
  destruct Step.
  apply gss.
  unfold le''. rewrite gso. rewrite gso. apply gss.
  1-2: cbv; congruence.
  replace (S len + i)%nat with (len + S i)%nat by omega.
  assumption.
      
Admitted.

Lemma strlen_loop_correct_gen : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false -> (* TODO: remove this assumption *)
  forall len i ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs + Z_of_nat len + Z_of_nat i < Ptrofs.modulus ->   
                       
       (* Precondition: reading C string of length len from memory *)
    strlen_mem m b ofs (len + i) ->
              
    exists t le', 
      exec_stmt ge e (PTree.set _output (VintN i) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))  le)) m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (len + i)).
Proof.
  induction len.
  intros until le.
  intro L.
  intros.
  repeat eexists.
   eapply exec_Sloop_stop1.
   seq2. seq1. seq1. repeat econstructor. rewrite gso. eapply gss. cbv; congruence.
   repeat econstructor.
   apply gss. repeat econstructor.
   repeat econstructor.
  rewrite gso. apply gss. cbv. congruence.
  simpl in H5.
  pose (S := strlen_trans_len_0 i m b ofs H5).
  inversion_clear S.
  simpl. 

  ptrofs_to_Z. apply H6. lia.
  apply gss.
  simpl.
  econstructor.
  replace (negb (Int.eq (Int.repr 0) Int.zero)) with false by simpl.      
  econstructor.
  cbv; congruence. econstructor.
  rewrite gso. rewrite gso. rewrite gso. replace (0 + i)%nat with i by lia. apply gss. 1-3: cbv; congruence.
  intros.
  assert (exists p, Mem.load Mint8unsigned m b (ofs + Z.of_nat i) = Some (VintP p)) as M.
  { refine (strlen_to_mem (S len + i) m b ofs H6 i _).
  omega. } 
  (* follows from spec H5 *)
  destruct M as [p M].
  pose (IH := IHlen (S i) ge e m b ofs (
       (PTree.set _t'2 (VintP p)
          (
             (PTree.set _t'1
                (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                (PTree.set _output (VintN i)
                   (PTree.set _input
                      (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                      le))))))).
  
  assert ( exists (t : trace) (le' : temp_env),
       exec_stmt ge e
         (PTree.set _output (VintN (S i))
            (PTree.set _input
               (Vptr b (Ptrofs.repr (ofs + Z.of_nat (S i))))
               (PTree.set _t'2 (VintP p)
                  (PTree.set _t'1
                     (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                     (PTree.set _output (VintN i)
                        (PTree.set _input
                           (Vptr b
                              (Ptrofs.repr (ofs + Z.of_nat i)))
                           le)))))) m f_strlen_loop t le' m
         Out_normal /\
       le' ! _output = Some (VintN (len + S i)) ) as Step.
  { pose (Ptrofs.modulus_eq32 H).
  eapply IH.
  1-6: lia.
  replace (len + S i)%nat with (S len + i)%nat by omega.
  assumption. }

  destruct Step as [s St]. destruct St as [t St]. destruct St as [St C].     
  (* do one loop *)
  repeat eexists.
  loop. repeat econstructor.
  rewrite gso.
  eapply gss. cbv ; congruence.
  apply gss.
  repeat econstructor.
  rewrite gso. apply gss. cbv. congruence. simpl. ptrofs_to_Z.
  
  apply M. lia.
  apply gss.
  econstructor.
  replace (negb (Int.eq (Int.repr (Z.pos p)) Int.zero)) with true. (* add lemma *)
  econstructor.
  {
    assert ( (Int.eq (Int.repr (Z.pos p)) Int.zero) = false).
    rewrite Int.eq_false.
    reflexivity.
    unfold Int.zero.
    assert (0 <> Z.pos p) by lia.
    
    pose (Int.eqm_samerepr (Z.pos p) 0).
    unfold not.
    intro.
    pose (Int.eqm_small_eq (Z.pos p) 0).
    unfold not in H7.

    SearchAbout Int.zero.
    
    admit.
     }
  rewrite gso. rewrite gso. rewrite gso. apply gss. 1-3: cbv ;congruence.
  repeat econstructor. econstructor. econstructor.
  fold f_strlen_loop.
  replace  (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)))
       (PTree.set _t'2 (VintP p)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat i))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tuchar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                (PTree.set _output (VintN i)
                   (PTree.set _input
                      (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                      le)))))) with (PTree.set _output (VintN (S i))
            (PTree.set _input
               (Vptr b (Ptrofs.repr (ofs + Z.of_nat (S i))))
               (PTree.set _t'2 (VintP p)
                  (PTree.set _t'1
                     (Vptr b (Ptrofs.repr (ofs + Z.of_nat i)))
                     (PTree.set _output (VintN i)
                        (PTree.set _input
                           (Vptr b
                              (Ptrofs.repr (ofs + Z.of_nat i)))
                           le)))))).
  
  eapply St.

  {
    replace (Vint (Int.add (Int.repr (Z.of_nat i)) (Int.repr 1))) with (VintN (S i)) by admit.
    replace (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat i))
                (Ptrofs.mul (Ptrofs.repr (sizeof ge tuchar))
                            (ptrofs_of_int Signed (Int.repr 1)))) with
        (Ptrofs.repr (ofs + Z.of_nat (S i))) by admit.

    
    admit.
  }

  replace (S len + i)%nat with (len + S i)%nat by omega.
  assumption.
      
Admitted.

Lemma strlen_loop_correct :
   Archi.ptr64 = false ->
   forall len ge e m b ofs le,
     
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
    strlen_mem m b ofs len ->
              
    exists t le', exec_stmt ge e (PTree.set _output (VintN O) (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le)) m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN len).
Proof.
  intros.
  Check strlen_loop_correct.
  replace ofs with (ofs + Z.of_nat O) by lia.
  replace len with (len + O)%nat by lia.
  eapply (strlen_loop_correct H len O ge e m b ofs le).
  1-6: lia.
  replace (len + O)%nat with len by omega.
  assumption.
Qed.
  
(* Full correctness statement *)
Lemma strlen_correct : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  
  forall len ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
                       (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->
                       
       (* Precondition: reading C string of length len from memory *)
    strlen_mem m b ofs len ->
               
      exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN len),tuint))).
Proof.
  (* follows from strlen_loop_correct *)
   Admitted.
               

