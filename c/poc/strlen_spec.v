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
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->                      
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->                     
    (* Precondition: reading empty C string from memory *)
    strlen_mem m b ofs O ->
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintZ 0).
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
      
        replace  (Ptrofs.unsigned
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
        cbv ; congruence.
        econstructor.
      * (* return statement *)
        repeat econstructor.  rewrite gso.  rewrite gso.  rewrite gso.  eapply gss. all: cbv ; congruence.
  - rewrite gso.  rewrite gso.  rewrite gso.  eapply gss. all: cbv ; congruence.
Admitted.

(* Conditions about the f_strlen loop *)

(* If 0 is read from memory at [b,ofs + len] the output is set to len *)
Lemma strlen_loop_break_correct : Archi.ptr64 = false -> forall ge e m b ofs outp le,
      
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
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
  seq1.
  seq1. repeat econstructor. apply H3. apply gss.
  repeat econstructor.
  seq1. repeat econstructor.
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


Lemma strlen_loop_continue_correct : (* with this assumption Ptrofs.modulus = Int.modulus, otherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall len ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) ->
    le!_output = Some (VintN len) ->
    
     (* Memory reads *)
      (exists p, Mem.load chunk m b (ofs + Z.of_nat len) = Some (VintP p)) ->
                                         
      exists t lef, exec_stmt ge e le m f_strlen_loop t lef m Out_normal ->  exists t les, exec_stmt ge e les m f_strlen_loop t lef m Out_normal /\ les!_output = Some (VintN (S len)).
Proof.
  intros.
  destruct H5 as [p].
  eexists.
  eexists.
  intro.
  eexists.
  exists (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat len)) (Int.repr 1)))
       (PTree.set _t'2 (VintP p)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat len))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tuchar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                        (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) le)))).
  split.
  - solve_by_inverts 5%nat.  solve_by_inverts 5%nat. 
  repeat eexists.
(*   exists t lef, exec_stmt ge e le m f_strlen_loop t lef m Out_normal ->  exists t les, exec_stmt ge e les m f_strlen_loop t lef m Out_normal /\ les!_output = Some (VintN (S len)). *)

Lemma strlen_loop_continue_correct : (* with this assumption Ptrofs.modulus = Int.modulus, otherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall len ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) ->
    le!_output = Some (VintN len) ->
    
     (* Memory reads *)
      (exists p, Mem.load chunk m b (ofs + Z.of_nat len) = Some (VintP p)) ->
                                         
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ le'!_output = Some (VintN (S len)).
Proof.
  intros.
  destruct H5 as [p].
  (* (PTree.set _output
       (Vint (Int.add (Int.repr (Z.of_nat len)) (Int.repr 1)))
       (PTree.set _t'2 (VintP p)
          (PTree.set _input
             (Vptr b
                (Ptrofs.add (Ptrofs.repr (ofs + Z.of_nat len))
                   (Ptrofs.mul
                      (Ptrofs.repr (sizeof ge tuchar))
                      (ptrofs_of_int Signed (Int.repr 1)))))
             (PTree.set _t'1
                (Vptr b (Ptrofs.repr (ofs + Z.of_nat len))) le))))*)
  repeat eexists.
  loop. repeat econstructor. repeat gso_assumption. eapply gss. repeat econstructor.
  rewrite gso. apply gss. cbv; congruence. simpl. ptrofs_to_Z. apply H5. lia.  
  apply gss.
  simpl.
  econstructor.
  replace (negb (Int.eq (Int.repr (Z.pos p)) Int.zero)) with true by admit.      
  econstructor.
  repeat (rewrite gso).
  apply H4. 1-3: cbv; congruence.
  repeat econstructor.
  econstructor.
  econstructor.
  loop.
  repeat econstructor.
  Print exec_stmt.
  
  rewrite gso. rewrite gso. apply gss. 1-3: cbv ;congruence.
  repeat econstructor. econstructor. econstructor.
  
  
Lemma strlen_loop_correct : (* with this assumption Ptrofs.modulus = Int.modulus, otherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall len ge e m b ofs le,
                       
    (* Preconditions on the length of the string and valid offset *)
    0 <= ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
    (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ len) ->
    
     (* Memory reads *)
    (forall i, (i < len)%nat ->
           exists p, Mem.load chunk m b (ofs + Z.of_nat i) = Some (VintP p)) ->
           Mem.load chunk m b (ofs + Z.of_nat len) = Some (VintN O) ->
                                          
      exists t le', exec_stmt ge e le m f_strlen_loop_new t le' m Out_normal /\ le'!_out = Some (VintN len) /\ strlen_mem_u m b ofs len.
Proof.
   induction len ; intros.
   (* Base case *)
   - repeat eexists.
     eapply exec_Sloop_stop1. seq2. repeat econstructor. apply H3. apply gss.
     repeat econstructor.
     rewrite gso. apply gss. cbv ; congruence.
     simpl. 
     replace  (Ptrofs.unsigned (Ptrofs.repr ofs)) with (ofs + Z.of_nat 0) by admit.
     apply H6.
     (* provable *) all: admit.
   
  (* Inductive Step *)  
   - 
     (*  pose (strlen_trans4 (S len) m b ofs H5).
      assert (forall i ofs len, (exists t, exec_stmt ge e  (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) le) m f_strlen_loop t (PTree.set _output (VintN len) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) le)) m Out_normal) -> (exists t, exec_stmt ge e  (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le) m f_strlen_loop t
       (PTree.set _output (VintN (len + i)%nat) (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le)) m
       Out_normal)).
      { induction i.
        - (* Base case *)
          intros ofs0 len0.
          replace (ofs0 + Z.of_nat 0) with ofs0 by lia.
          replace (len0 + 0)%nat with len0 by lia.
          auto.
        - (* I.S.*)
          intros.
          pose (IHi (ofs0 + 1) len0).
          replace (ofs0 + 1 + Z.of_nat i) with (ofs0 + Z.of_nat (S i)) in e1 by lia.
          pose (e1 H6).
          replace (len0 + S i)%nat with (len0 + 1 + i)%nat by lia.
          apply (IHi (ofs0) (len0 + 1)%nat). admit. } *)
    (*  pose (H6 1%nat ofs len).
      replace (len + 1)%nat with (S len) in e1 by omega.
      replace le with (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le) by admit.
      apply e1. *)
     pose (IHlen ge e m b (ofs + 1)  (PTree.set _in (Vptr b (Ptrofs.repr (ofs + 1))) le)).

    assert (0 <= ofs + 1 < Ptrofs.modulus) by lia.
    assert (Z.of_nat len < Int.modulus) by lia.
    assert (ofs + 1 + Z.of_nat len < Ptrofs.modulus) by lia.
    assert ((PTree.set _in (Vptr b (Ptrofs.repr (ofs + 1))) le) ! _in =
     Some (Vptr b (Ptrofs.repr (ofs + 1)))) by (apply gss).
    assert ((PTree.set _in (Vptr b (Ptrofs.repr (ofs + 1))) le) ! _out = Some (VintZ 0)) by admit.
    assert (forall i : nat,
      (i < len)%nat ->
      exists p : positive, Mem.load chunk m b (ofs + 1 + Z.of_nat i) = Some (VintP p)) by admit.
    pose (e0 H7 H8 H9 H10 H11 H12).
    replace (ofs + 1 + Z.of_nat len) with (ofs + Z.of_nat (S len)) in e1 by lia.
    pose (e1 H6).
    destruct e2. destruct H13. destruct H13. destruct H14.
    repeat eexists
    

     loop. repeat econstructor. repeat gso_assumption. eapply gss. repeat econstructor.
        rewrite gso. apply gss. cbv. congruence. simpl. ptrofs_to_Z. apply H7. assumption.
        apply gss.
        simpl.
        econstructor.
        replace (negb (Int.eq (Int.repr (Z.pos v)) Int.zero)) with true by admit.      
        econstructor.
        rewrite gso. rewrite gso. rewrite gso. apply H4.  1-3: cbv ;congruence.
        repeat econstructor. econstructor. econstructor.
        
    
          (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)  _ _ _ _ _ _). 1-3: nia.  apply gss. gso_assumption. assumption. gso_assumption.
  inversion_clear H5.
      assumption. 
Admitted. *)

Lemma strlen_loop_correct : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
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
    strlen_mem_u m b ofs len ->
               
      exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN len) le) m Out_normal.
Proof.
   induction len ; intros.
   (* Base case *)
   -
     (* assert ((PTree.set _output (VintN 0) le) = le). (* true *)
     admit.
     rewrite H6.  
     eapply (strlen_correct_loop_empty_string1 _ _ _ _ _ ofs _ O). 1-3: nia. 1,2: gso_assumption. assumption.
    *) admit.
  (* Inductive Step *)  
   -  pose (strlen_trans4 (S len) m b ofs H5).
      assert (forall i ofs len, (exists t, exec_stmt ge e  (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) le) m f_strlen_loop t (PTree.set _output (VintN len) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + Z.of_nat i))) le)) m Out_normal) -> (exists t, exec_stmt ge e  (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le) m f_strlen_loop t
       (PTree.set _output (VintN (len + i)%nat) (PTree.set _input (Vptr b (Ptrofs.repr (ofs))) le)) m
       Out_normal)).
      { induction i.
        - (* Base case *)
          intros ofs0 len0.
          replace (ofs0 + Z.of_nat 0) with ofs0 by lia.
          replace (len0 + 0)%nat with len0 by lia.
          auto.
        - (* I.S.*)
          intros.
          pose (IHi (ofs0 + 1) len0).
          replace (ofs0 + 1 + Z.of_nat i) with (ofs0 + Z.of_nat (S i)) in e1 by lia.
          pose (e1 H6).
          replace (len0 + S i)%nat with (len0 + 1 + i)%nat by lia.
          apply (IHi (ofs0) (len0 + 1)%nat). admit. }
      pose (H6 1%nat ofs len).
      replace (len + 1)%nat with (S len) in e1 by omega.
      replace le with (PTree.set _input (Vptr b (Ptrofs.repr ofs)) le) by admit.
      apply e1.
      refine (IHlen ge e m b (ofs + 1) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)  _ _ _ _ _ _). 1-3: nia.  apply gss. gso_assumption. assumption. gso_assumption.
  inversion_clear H5.
      assumption. 
Admitted.

(* Alternative loop correctness statement *)

Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall outp ge e m b ofs le,
      
      1 <= Z.of_nat (S outp) < Ptrofs.modulus ->
      ofs + Z.of_nat (S outp) < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (VintN outp) ->
      
      (forall i, (i <= outp)%nat -> exists p, Mem.load Mint8signed m b (ofs + (Z_of_nat i)) = Some (VintP p)) -> exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN (S outp)) le) m Out_normal.
Proof.
Admitted.


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
  intros.
  destruct (strlen_loop_correct H len ge e _ _ _ _ H0 H1 H2 H3 H4 H5).
  eexists.
  exists (PTree.set _output (VintN len) le). 
   -- seq1.
         + seq1.
           * sset. repeat econstructor.
           * fold f_strlen_loop.            
             
              assert ((PTree.set _output (Vint (Int.repr 0)) le) = le). 
              { admit. (* true *) }
              rewrite -> H7.
              apply H6.
         + repeat econstructor. apply gss.
   Admitted.
               

