(** This is a toy example to demonstrate how to specify and prove correct a C function using C light *)


From Coq Require Import String List ZArith Psatz.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs Memory Values ClightBigstep Events Maps.
(* Local Open Scope Z_scope.*)


(** High-level functional specification *)

Inductive string_length : string -> nat -> Prop :=
| ZeroLen : string_length EmptyString 0
| SuccLen : forall (n : nat) (s : string) (c : Ascii.ascii) , string_length s n -> string_length (String c s) (S n).
    
Definition strlen_fun := String.length.

Parameter strlen_fun_correct : forall (s : string), string_length s (strlen_fun s).

(* Strings as list of bytes *)

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Definition strlen_byte (bs : list byte) := List.length bs.

Definition c_string (s : string) := (string_to_list_byte s)++(Byte.repr 0)::nil.
Definition example := c_string "Hello".

Lemma length_string_byte_equiv : forall s, String.length s = strlen_byte (string_to_list_byte s).
Proof.
  induction s.
  - simpl. reflexivity.
  - simpl. rewrite <- IHs. reflexivity.
Qed.

Parameter strlen_byte_correct : forall (s : string), string_length s (strlen_byte (string_to_list_byte s)).

(* Connection high-level and low-level specification *)

(* Address (b,ofs) is a block b an offset ofs *)

Definition addr : Type := (Values.block*Z).
Definition block_of (addr : addr) := match addr with (b,_) => b end.
(* Valid block in m *)
Definition valid_block_b (m : mem) (b : Values.block):=
  plt b (Memory.Mem.nextblock m).

(* Assume the low-level spec outputs the values read *)
Parameter strlen_C_byte : mem -> addr -> option (Z*mem*list byte).

Definition strlen_C_correct := forall m p z m' bs, strlen_C_byte m p = Some (z,m',bs) -> Z.of_nat (strlen_byte bs) = z.

(** Low-level specification *)

(* true if the integer value read is zero - end of string *)
Definition is_null (v : Values.val) :=
  match v with
  | Vint zero => true
  | _ => false
  end.


Definition chunk : memory_chunk := Mint8signed. (* that's what we read from memory *)
Definition INTSIZE := (nat_of_Z Int.modulus).

Fixpoint strlen_fun_C (m : mem) (b : block) (ofs : Z) (l: Z) (intrange : nat) {struct intrange} : option (Z*mem):= (* maybe nat output? *)
      match intrange with
      | O => None (* out of int range *)
      | S n => match Mem.load chunk m b ofs with (*  loading value from memory *)
              | Some v =>
                if is_null v
                then Some (l, m) else strlen_fun_C m b (ofs + 1) (l + 1) n  
              | None => None (* address not readable or b not allocated *)
              end
      end.

Definition strlen_C_fun_spec (m : mem) (b: block) (ofs : Z) :=  strlen_fun_C m b ofs 0 INTSIZE.

(* Coercion Int.intval : Int.int >-> Z.*)

Definition VintZ := fun (z : Z) => Vint (Int.repr z).
Definition VintN:= fun n => Vint (Int.repr(Z_of_nat n)).

Notation gso := PTree.gso.
Notation gss := PTree.gss.

(* Recursive spec *)

(* unsigned C char *)
Definition C_uchar : Set := positive.
  
Inductive C_string : Set :=
| CEmptyString : C_string
| CString : positive -> C_string -> C_string.

Inductive strlen : C_string -> nat -> Prop :=
| LengthZero : strlen CEmptyString 0
| LengthSucc : forall n s c, strlen s n -> strlen (CString c s) (S n).

Definition VintP := fun p : positive => Vint (Int.repr (Z.pos p)).

(* Inductive strlen_mem_op : mem -> block -> Z -> option (C_string*nat) -> Prop :=
| LengthZeroMem_op : forall m b ofs, Mem.load Mint8signed m b ofs = Some (VintZ 0) -> strlen_mem_op m b ofs (Some (CEmptyString, O))
| LengthSuccMem_op : forall m b ofs c s n, strlen_mem_op m b (ofs + 1) (Some (s,n)) -> Mem.load Mint8signed m b ofs = Some (VintP c) -> strlen_mem_op m b ofs (Some ((CString c s),(S n))).
*)

 Inductive strlen_mem : mem -> block -> Z -> nat -> Prop :=
| LengthZeroMem m b ofs: Mem.load Mint8signed m b ofs = Some (VintZ 0) -> strlen_mem m b ofs 0
| LengthSuccMem m b ofs: forall p v,
    strlen_mem m b (ofs+1) p ->
    Mem.load Mint8signed m b ofs = Some (VintP v) ->
    strlen_mem m b ofs (S p).

(* Semantics of a C light function: *)

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
    Mem.load chunk m b ofs = Some (VintN O) ->
    (* C light expression f_strlen returns O and assigns O to output variable *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN O),tuint))) /\ (le'!_output) = Some (VintN O).
Proof.
  intros.
  repeat eexists.
  - seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * eapply exec_Sloop_stop1. (* break from the loop *)
        repeat econstructor. repeat gso_assumption. 
        eapply gss. 
        repeat econstructor. simpl.
        replace (Ptrofs.unsigned
                   (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. apply H5.
        { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul.  all: nia. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
  - eapply gss.
Qed.

(* On empty string then C light function evaluates to 0 *)
Lemma strlen_correct_empty_string_recursive :
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

Lemma strlen_loop_break_correct2 : Archi.ptr64 = false -> forall ge e m b ofs outp le,
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
          | _ => idtac
        end.    


 Ltac solve_by_inverts n :=
   match n with
   | O => subst
   | S (?n') =>  invert_clear; solve_by_inverts n'
   end.


(* Lemma used in the induction step below *)

(* if executing f_strlen_loop with output = 0 and input = [b,ofs + 1] outputs len
    then executing f_strlen_loop with output = 0 and input = [b,ofs] outputs (S outp) *)
Lemma exec_trans : forall ge e le m b ofs len,   
    le!_output = Some (VintZ 0) ->
    
    (exists t, exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le) m f_strlen_loop t  (PTree.set _output (VintN len)(PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)) m Out_normal) ->

    le ! _input = Some (Vptr b (Ptrofs.repr ofs)) ->
    (exists p : positive, Mem.load chunk m b ofs = Some (VintP p)) ->
    (exists t, exec_stmt ge e le m f_strlen_loop t (PTree.set _output (VintN (S len)) le) m Out_normal).
Proof.
  intros.
  invert_clear.
  invert_clear.
  invert_clear.
  invert_clear.
  invert_clear. invert_clear. invert_clear. invert_clear.
  invert_clear. invert_clear. invert_clear. invert_clear. invert_clear. invert_clear. invert_clear. invert_clear. 
  
    eexists.
      loop. repeat econstructor. repeat gso_assumption. gso_assumption. repeat econstructor. simpl. replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with (ofs).
   apply H2.
  {  ptrofs_compute_add_mul. all: admit. } repeat econstructor. simpl. repeat econstructor. simpl.
        replace (negb (Int.eq (Int.repr (Z.pos x)) (Int.repr 0))) with true.      
        econstructor. admit. repeat econstructor. econstructor. repeat econstructor. apply H. 
       repeat econstructor.
       fold f_strlen_loop.

       replace (Int.add (Int.repr 0) (Int.repr 1)) with (Int.repr 1) by (auto with ints).
       

       
  Admitted.

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

  assert (exists t, exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le) m f_strlen_loop t
       (PTree.set _output (VintN len) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)) m
       Out_normal).
  
  (* assert (exists (t : trace) (le' : temp_env),
            exec_stmt ge e (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le) m f_strlen_loop t le' m Out_normal /\
            le' ! _output = Some (VintN len)). *)
  refine (IHlen ge e m b (ofs + 1) (PTree.set _input (Vptr b (Ptrofs.repr (ofs + 1))) le)  _ _ _ _ _ _). 1-3: nia.  apply gss. gso_assumption. assumption. gso_assumption.
  inversion_clear H5.
  assumption.
  destruct H6. (* destruct H6. destruct H6. *)

  (* using lemmas *)
  assert (0 < S len)%nat as L by omega.
  destruct (e0 O L).  replace (ofs + Z.of_nat 0) with ofs in H7 by nia.  
  repeat eexists.
     -- pose (exec_trans ge e le m x b ofs len H4).
        assert (exists p : positive,
        Mem.load chunk m b ofs = Some (VintP p)) as J. exists x0. assumption.
        pose (e1 H6 H3 J).
        apply e2.  
Admitted.        

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
  destruct ( strlen_loop_correct H len ge e _ _ _ _ H0 H1 H2 H3 H4 H5).
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
               

