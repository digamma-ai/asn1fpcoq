(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
(* Local Open Scope Z_scope.*)

(* Some useful notation and tactics *)

Definition chunk : memory_chunk := Mint8signed.
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
| LengthZeroMem m b ofs: Mem.load Mint8signed m b ofs = Some (VintZ 0) -> strlen_mem m b ofs 0
| LengthSuccMem m b ofs: forall p v,
    strlen_mem m b (ofs+1) p ->
    Mem.load Mint8signed m b ofs = Some (VintP v) ->
    strlen_mem m b ofs (S p).

(* strlen C light AST *)

Definition _i : ident := 54%positive.
Definition _s : ident := 53%positive.
Definition _strlen : ident := 55%positive.

Notation _input := _s.
Notation _output := _i.

Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Sifthenelse (Ebinop One
                     (Ederef
                       (Ebinop Oadd (Etempvar _s (tptr tschar))
                         (Etempvar _i tuint) (tptr tschar)) tschar)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Sreturn (Some (Etempvar _i tuint))))
                      |}.


(* Loop of f_strlen *)

Definition f_strlen_loop :=  (Sloop
      (Sifthenelse (Ebinop One (* comparison ([!=]) *)
                     (Ederef (* pointer dereference (unary [*]) *)
                       (Ebinop Oadd (Etempvar _input (tptr tschar))
                         (Etempvar _output tuint) (tptr tschar)) tschar)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Sset _output
        (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint)
                tuint))).

(* Correctness statements *)

(* On empty string then C light function evaluates to 0 *)
Lemma strlen_correct_empty_string :
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
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN O),tuint))) /\ (le'!_output) = Some (VintN O).
Proof.
  intros.
  inversion H5.
  repeat eexists.
  - seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * eapply exec_Sloop_stop1. (* break from the loop *)
        repeat econstructor. repeat gso_assumption. 
        eapply gss. 
        repeat econstructor. simpl.
        replace (Ptrofs.unsigned
                   (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H6.
        { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
  - eapply gss.
Qed.


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
    exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ (le'!_output) = Some (VintN O).
Proof.
  intros.
  inversion_clear H5.
  repeat eexists.
  - eapply exec_Sloop_stop1. (* break from the loop *)
    repeat econstructor. 1,2: gso_assumption.
    repeat econstructor. simpl.
    replace (Ptrofs.unsigned
               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs.  apply H6. { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
   repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.    
  - assumption.
Qed.


Lemma strlen_correct_loop_empty_string1 :
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
    exists t, exec_stmt ge e le m f_strlen_loop t le m Out_normal.
Proof.
  intros.
  inversion_clear H5.
   eexists.
  - eapply exec_Sloop_stop1. (* break from the loop *)
    repeat econstructor. 1,2: gso_assumption.
    repeat econstructor. simpl.
    replace (Ptrofs.unsigned
               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H6. { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
   repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.    

Qed.

 
(* Conditions about the f_strlen loop *)

(* If 0 is read from memory at [b,ofs + len] the output is set to len *)
Lemma strlen_loop_break_correct : Archi.ptr64 = false -> forall ge e m b ofs outp le,
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (VintN outp) -> 
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\
        (le'!_output) = Some (VintN outp).
Proof.
  intros.
  repeat eexists.
  - eapply exec_Sloop_stop1.
    repeat econstructor; repeat gso_assumption. 
    repeat econstructor. simpl.
    replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) with (ofs + (Z_of_nat outp)). apply H5.
        { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
  - assumption.
Qed.

Lemma strlen_loop_break_correct1 : Archi.ptr64 = false -> forall ge e m b ofs outp le,
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (VintN outp) ->
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->
      exists t, exec_stmt ge e le m f_strlen_loop t le m Out_normal.
Proof.
   intros.
  repeat eexists.
  - eapply exec_Sloop_stop1.
    repeat econstructor; repeat gso_assumption. 
    repeat econstructor. simpl.
    replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) with (ofs + (Z_of_nat outp)). apply H5.
        { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
Qed.


(* Some tests *)

(* On a string of length 2 C light function evaluates to 0 *)
Lemma strlen_correct_test :
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
    (* Precondition: reading  C string of length 2 from memory *)
    strlen_mem m b ofs 2%nat ->
    
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintZ 2),tuint))) /\ (le'!_output) = Some (VintZ 2).
Proof.
  intros.
  inversion_clear H5. inversion_clear H6. inversion_clear H5.
  repeat eexists.
  - seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl. replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H7.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. } repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos v)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. repeat econstructor. repeat econstructor. apply gss. repeat econstructor.

        (* loop 2 *)
        loop. repeat econstructor. rewrite gso; repeat gso_assumption. eapply gss.
        repeat econstructor. simpl. replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.add (Int.repr 0) (Int.repr 1)))))) with (ofs + 1). apply H8.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: admit. }        repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos v0)) (Int.repr 0))) with true.
      
        econstructor. repeat econstructor. repeat econstructor. admit.  econstructor. repeat econstructor. repeat econstructor. apply gss. repeat econstructor.
         (* exit loop *)
        eapply exec_Sloop_stop1. (* break from the loop *)
        repeat econstructor.  rewrite gso; repeat gso_assumption.  rewrite gso; repeat gso_assumption.  eapply gss.
        repeat econstructor. simpl.
        replace  (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
          (Ptrofs.mul (Ptrofs.repr 1)
             (Ptrofs.of_intu (Int.add (Int.add (Int.repr 0) (Int.repr 1)) (Int.repr 1)))))) with (ofs + 2). replace (ofs + 2) with (ofs + 1 + 1) by lia. apply H6. { admit. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
  - eapply gss.
Admitted.


(* Helper lemmas about strlen_mem *)

Lemma strlen_trans1 : forall len m b ofs, strlen_mem m b ofs len -> strlen_mem m b (ofs + Z.of_nat len) O.
Proof.
  induction len ; intros.
  - replace (ofs + Z.of_nat 0) with ofs by nia. assumption.
  - inversion_clear H.
    replace (ofs + Z.of_nat (S len)) with (ofs + 1 + Z.of_nat len) by nia.
    apply (IHlen m b (ofs + 1) H0).
Qed.

Lemma strlen_trans3 : forall len m b ofs, strlen_mem m b ofs len -> forall i, (i < len)%nat -> strlen_mem m b (ofs + Z.of_nat i) (len - i)%nat.
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
   
Lemma strlen_trans4 : forall len m b ofs, strlen_mem m b ofs len ->
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
    strlen_mem m b ofs len ->
               
      exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN len) le) m Out_normal.
Proof.
   induction len ; intros.
   (* Base case *)
   -
     assert ((PTree.set _output (VintN 0) le) = le). (* true *)
     admit.
     rewrite H6.  
     eapply (strlen_correct_loop_empty_string1 _ _ _ _ _ ofs _ O). 1-3: nia. 1,2: gso_assumption. assumption.
   
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
               

