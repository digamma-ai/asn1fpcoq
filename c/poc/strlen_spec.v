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

(* Definition tschar := Tint I8 Signed noattr.
Definition tuchar := Tint I8 Unsigned noattr.
 *)

Locate typ.

(* Try recursive definition *)

Inductive C_char : nat -> Set :=
| Null_char : C_char 0
| Not_null_char : forall n, C_char (S n).

Check (Not_null_char 0).
Check (C_char 1).


(* Idea : take C_string to be nat *)

(* Inductive C_string (m : Mem.mem) (b : block) (ofs : nat) : nat -> Prop :=
| Empty_C_string : Mem.load Mint8signed m b (Z.of_nat ofs) = Some (VintZ 0) -> C_string m b ofs 0
| Succ_C_string : forall v, C_char v -> Mem.load Mint8signed m b (Z.of_nat (S ofs)) = Some (VintZ 0) ->
                       Mem.load Mint8signed m b (Z.of_nat ofs) = Some v ->
                        C_string m b ofs ofs. *)


Inductive pre_C_string (m : Mem.mem) (b : block) (ofs : Z) (len : nat) :=
  is_pre_C_string : forall n i, (0 < Z.of_nat n < Int.modulus) ->
                        (0 <= i <= len)%nat ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat i) = Some (VintN n) ->
                        pre_C_string m b ofs len.

Inductive C_string (m : Mem.mem) (b : block) (ofs : Z) : nat -> Prop :=
  | empty_C_string : Mem.load Mint8signed m b ofs = Some (VintZ 0) ->
                   C_string m b ofs O
  | non_empty_C_string : forall len, pre_C_string m b ofs len -> C_string m b (ofs + Z.of_nat (S len)) O -> C_string m b ofs len.                         

(* Inductive C_string (m : Mem.mem) (b : block) (ofs : Z) (len : nat) :=
  is_C_string : forall n i, (0 < Z.of_nat n < Int.modulus) ->
                        (0 <= i < len)%nat ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat i) = Some (VintN n) ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat len) = Some (VintZ 0) ->
                        C_string m b ofs len.

*)
Locate tschar.

(* Relational spec  *)

(*Inductive non_null_char : val -> Prop :=
  is_non_null_char : forall n, (0 < n)%nat -> non_null_char (VintN n).

Inductive pre_C_string : C_char -> Prop :=
  char_pre_C_string : Not_null_char.
  
  

Inductive strlen_C_rel_spec : Mem.mem -> block -> Z -> option (nat * mem)-> Prop
  :=

  | ReadEmptyString : forall m b ofs, Mem.load Mint8signed m b ofs = Some (VintZ 0) -> strlen_C_rel_spec m b ofs (Some (O, m))
  | ReadSuccString : forall m b ofs len,  Mem.load Mint8signed m b (ofs + len)  = Some (VintZ 0) ->
                                     forall i z, i < len -> 0 < z -> Mem.load Mint8signed m b (ofs + i) = Some (VintZ z) ->  strlen_C_rel_spec m b ofs (Some (
  | CorrectRun :  forall len m b ofs,
      (len < INTSIZE)%nat -> C_string m b ofs len ->  strlen_C_rel_spec m b ofs (Some (len,m))
  | OutOfRange : forall len m b ofs,
      (len > INTSIZE)%nat -> C_string m b ofs len ->  strlen_C_rel_spec m b ofs None.
 (*                                                                       
  | MemoryLoadFail : OutOfRange : forall len m b ofs,
      (len < INTSIZE)%nat -> Mem.load Mint8signed m b (ofs + Z_of_nat len) = None -> strlen_C_rel_spec m b ofs None
                                                                        
                                                                        
  | MemoryLoadZero : forall m b ofs,
              Mem.load chunk m b ofs = None ->
              strlen_C_rel_spec m b ofs None
  | MemoryLoadSucc : forall len m b ofs,
       (len < INTSIZE)%nat ->
      forall v, Mem.load chunk m b ofs = Some v ->
              Mem.load chunk m b (ofs + (Z_of_nat n)) = Some (Vint (Int.repr 0)) ->
              (exists n', (n' < n)%nat /\ Mem.load chunk m b (ofs + (Z_of_nat n')) = None) ->
              strlen_C_rel_spec m b ofs None.
  *)                                                                         
    *)                        
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

(* Big step semantics *)

Definition Vint_of_nat := fun n => Vint (Int.repr(Z_of_nat n)).

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


Notation gso := PTree.gso.
Notation gss := PTree.gss.

Ltac ints_to_Z :=
  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small.

Ltac ptrofs_to_Z :=
  repeat rewrite Ptrofs.unsigned_repr_eq; repeat rewrite Zmod_small.

 Ltac ptrofs_compute_add_mul :=
      simpl; unfold Ptrofs.add; unfold Ptrofs.mul; unfold Ptrofs.of_intu; unfold Ptrofs.of_int;
      repeat rewrite Ptrofs.unsigned_repr_eq;  repeat rewrite Int.unsigned_repr_eq; repeat rewrite Zmod_small; simpl.



Ltac seq1 := eapply exec_Sseq_1.
Ltac seq2 := eapply exec_Sseq_2.
Ltac sset := eapply exec_Sset.
Ltac loop := eapply exec_Sloop_loop.
Ltac gss := eapply gss.

Ltac gso_assumption :=
  match goal with
  | [ H : ?P ! ?I = Some ?W |- (PTree.set ?O _ ?P) ! ?I = Some ?Z ] => rewrite gso  
  | [ H : ?P ! ?Q = Some ?W |-  ?P ! ?Q = Some ?Z ] => apply H
  | [ |- _ <> _ ] => cbv ; congruence
  end.

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
        { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. }
        repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
  - eapply gss.
Qed.
 
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
  intro Arch.
  intros  ge e m b ofs outp le.
  intro S.
  intros.
  repeat eexists.
  - eapply exec_Sloop_stop1. eapply exec_Sifthenelse. econstructor. econstructor. econstructor.
    econstructor.
    econstructor.
    apply H1.
    econstructor.
    apply H2. econstructor. econstructor. econstructor. simpl.
    cut ( (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) = (ofs + (Z_of_nat outp)) ). intro aux. rewrite aux. apply H3.
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut.
      ptrofs_compute_add_mul ; nia. }
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
  - apply H2.
Qed.


Lemma strlen_loop_break_correct2 : Archi.ptr64 = false -> forall ge e m b ofs outp le,
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (VintN outp) ->
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr 0)) ->
      exists t , exec_stmt ge e le m f_strlen_loop t le m Out_normal.
Proof.
  intro Arch.
  intros  ge e m b ofs outp le.
  intro S.
  intros.
  repeat eexists.
  - eapply exec_Sloop_stop1. eapply exec_Sifthenelse. econstructor. econstructor. econstructor.
    econstructor.
    econstructor.
    apply H1.
    econstructor.
    apply H2. econstructor. econstructor. econstructor. simpl.
    cut ( (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) = (ofs + (Z_of_nat outp)) ). intro aux. rewrite aux. apply H3.
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut.
      ptrofs_compute_add_mul ; nia. }
    econstructor.
    econstructor.
    econstructor.
    replace (negb (Int.eq Int.zero Int.zero)) with false by simpl.
    eapply exec_Sbreak.
    econstructor.
Qed.


(* Proof attempts below *)

  


Lemma strlen_correct : Archi.ptr64 = false -> forall ge e m b ofs le len,
      
      (0 <= Z_of_nat len < Int.modulus ) -> (* len is within bounds *)
      0 < ofs < Ptrofs.modulus -> 
      (ofs + Z_of_nat len) < Ptrofs.modulus ->  (* the offsets are valid *)
  
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) -> (* input is an address [b,ofs] *) 
      le!_output = Some (VintZ 0) -> (* we start from 0 *)
      
      C_string m b ofs len -> (* [b,ofs] points to a string of length len in memory m *)
      
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m (Out_return (Some (VintN len, tuint))) /\
               (le'!_output) = Some (Vint_of_nat len).
(* the C light expression evaluates to outcome Out_return (Some VintN len) and output is set to len *)
Admitted.


Lemma strlen_corr2 : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,
                       
               (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat len < Int.modulus ->
    ofs + Z_of_nat len < Ptrofs.modulus ->
                       
                       (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->

                       
       (* Precondition: reading C string from memory *)
    forall i z, (i < len)%nat ->
           Mem.load chunk m b (ofs + Z.of_nat i) = Some (VintN (S z)) ->
           Mem.load chunk m b ofs = Some (VintN O) ->
           
      exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN len),tuint))) /\
                    (le'!_output) = Some (VintN len).
Proof.
  induction len.
  - (* Base case *) intro L. intros.
    apply (strlen_loop_break_correct H _  _ _ b ofs _ _).
    (* 1,2,3: nia. *)    
     all: try nia ; try assumption. inversion H3. simpl; unfold VintZ in H5; replace (ofs + 0) with ofs by lia. assumption. inversion H3. simpl; unfold VintZ in H5; replace (ofs + 0) with ofs by lia. assumption.
  - (* Induction Step *) intro L. intros.
    assert (C_string m b ofs len).
    { inversion H3. admit. }
    assert  (0 <= Z_of_nat len < Int.modulus ). { clear IHlen. lia. }
    assert (ofs + Z.of_nat len < Ptrofs.modulus). { clear IHlen. nia. }                                   
    pose (H8:= IHlen H7 H0 H1 H2 H5 H6).
    destruct H8. destruct H8. destruct H8. clear IHlen.
    assert  (exists t, exec_stmt ge e x0 m f_strlen_loop t (PTree.set _output (VintN (S len)) x0) m Out_normal /\ le ! _output = Some (Vint_of_nat (Datatypes.S len))).
    { repeat eexists.
      +  Print exec_stmt. eapply exec_Sloop_loop.
         repeat econstructor. Admitted.

Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall z ge e m b ofs outp le,
      
      1 <= Z.of_nat (S outp) < Ptrofs.modulus ->
      0 < z < Int.modulus ->
      ofs + Z.of_nat ( S outp ) < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (VintN outp) ->
      
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr z)) ->
      
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\
               (le'!_output) = Some (VintN (S outp)).
Proof.
  intros.
  eexists.
  exists (PTree.set _output (VintN (S outp)) le).
  split.
  + Print exec_stmt. eapply exec_Sloop_loop. repeat econstructor. apply H5. apply H6.
    econstructor. simpl. replace  (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) with (ofs + Z.of_nat outp). apply H7. { pose (Ptrofs.modulus_eq32 H). rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. ptrofs_compute_add_mul. all: nia. }
   econstructor. simpl. replace  (negb (Int.eq (Int.repr z) (Int.repr 0))) with true.
    econstructor.  admit.
    repeat econstructor.  econstructor.
    repeat econstructor. apply H6.
    repeat econstructor.
    assert (exists t, exec_stmt ge e (PTree.set _output (Vint (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1))) le)
    m
    (Sloop
       (Sifthenelse
          (Ebinop One
             (Ederef
                (Ebinop Oadd (Etempvar _input (tptr tschar)) (Etempvar _output tuint)
                   (tptr tschar)) tschar) (Econst_int (Int.repr 0) tint) tint) Sskip Sbreak)
       (Sset _output (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint) tuint)))
    t (PTree.set _output (Vint (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1))) le) m Out_normal ).
    
    fold f_strlen_loop. apply (strlen_loop_break_correct2 H _  _ _ b ofs (S outp) _) ; try nia ; try assumption. rewrite PTree.gso. assumption. cbv. congruence.    

    replace (Vint (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1))) with  (VintN (S outp)).
    apply PTree.gss.
    { unfold VintN. f_equal. unfold Int.add. ints_to_Z. f_equal. nia. nia. admit.
    (* from H0 *) }
    admit.
    replace (VintN (S outp)) with  (Vint (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1))).
    edestruct H8.
    admit.
    admit.
Admitted.
  
(* Old stuff: One direction of correctness, using functional spec, below relational with proof attempt *)

 Definition strlen_C_fun_corr_r :
  forall (ge :genv) (m : Mem.mem) (b : block) (ofs : Z) (e : env) (le : temp_env) (z : Z),
    strlen_C_fun_spec m b ofs = Some (z,m) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> (* input parameter _s assigned value of address (b,ofs) in le *)
    exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))) /\ le'!_i = Some (Vint (Int.repr z)).
               (* in environments ge, e (local env), le and memory m with output trace t, output _i assigned value z *)
Proof.
  intros.
  repeat eexists.
  (* econstructor can choose a wrong case in exec_stmt *)
  eapply exec_Sseq_1. eapply exec_Sseq_1. econstructor. econstructor.
  (* loop *)
  (* - apply Maps.PTree.gss.
    - repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply PTree.gss.
    + repeat econstructor. *)
Admitted.

 (* Find proofs on arithmetic on ptrofs type to rewrite this *)
      Hypothesis ptr_ofs_eq : forall ofs, ofs = (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))). 

      
Definition strlen_C_rel_corr_r : forall n m b ofs e le ge,
    strlen_C_rel_spec m b ofs (Some (n,m)) ->
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> 
    exists t le', le'!_i = Some (Vint_of_nat n) /\ 
           exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((Vint_of_nat n),tuint))).
Proof.
  induction n.
  (* Base case. *)
    intros.
    inversion H. unfold chunk in *. destruct H4.
    eexists.
    exists (Maps.PTree.set _i (Vint (Int.repr (Z.of_nat 0))) le).
    split.
    - apply Maps.PTree.gss.
    - repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply PTree.gss.
    + repeat econstructor.
    + simpl. rewrite <- ptr_ofs_eq. apply H3.
    + cbn. rewrite -> H4. reflexivity.
    + cbn. unfold Val.of_bool. simpl in H8. rewrite H4 in H3.  rewrite Z.add_0_r in H8.  rewrite H8 in H3. inversion H3. reflexivity.
    + Hypothesis fls : negb (Int.eq Int.zero Int.zero) = false.
      rewrite fls. econstructor.
    + apply PTree.gss.
      (* Ind step *)
     -   intros.
        inversion H. unfold chunk in *. destruct H4.
        eexists.
        exists (Maps.PTree.set _i (Vint (Int.repr (Z.of_nat (S n)))) le).
    split.
      + apply Maps.PTree.gss.
    + repeat econstructor.
     rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
     apply PTree.gss.
     repeat econstructor.
     simpl. rewrite <- ptr_ofs_eq. apply H3.
     cbn. rewrite -> H4. reflexivity.
     cbn. unfold Val.of_bool. simpl in H8. rewrite H4 in H3. destruct (negb (Int.eq x (Int.repr 0))). simpl.  Hypothesis tr : negb (Int.eq Int.one Int.zero) = true. rewrite tr. constructor. simpl. rewrite fls. (* false goal: prove the correctness of the loop *) 
Admitted.

(* Tactic for inversion  *)

 Ltac invertSem :=
        match goal with
          | [H : context[exec_stmt] |- _] =>
            inversion H ; clear H 
          | [H : context[eval_expr] |- _] =>
            inversion H ; clear H
          | [H : context[eval_lvalue] |- _] =>
            inversion H ; clear H 
          | [H : context[bool_val] |- _] =>
            inversion H ; clear H
          | [H : context[deref_loc] |- _] =>
            inversion H ; clear H  
          | [H : context[sem_binary_operation] |- _] =>
            inversion H ; clear H  
          | [H : context[access_mode] |- _] =>
            inversion H ; clear H  
          | _ => idtac
        end.    
 

 Ltac solve_by_inverts n :=
   match n with
   | O => idtac
   | S (?n') => invertSem ; subst ; solve_by_inverts n'
   end.

 (* behaves differently than the above: 

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

  *)
 
 Definition strlen_C_rel_corr_l : forall n m b ofs e le,
     (n < INTSIZE)%nat ->
     le!_s = Some (Vptr b (Ptrofs.repr ofs)) ->
     (exists le', le'!_i = Some (Vint (Int.repr (Z_of_nat n))) /\ 
                bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr (Z_of_nat n)),tuint))))
           -> strlen_C_spec m b ofs (Some (n,m)).
Proof.
  intros.
  repeat destruct H1.
  inversion H2.
  solve_by_inverts 5%nat. solve_by_inverts 15%nat. (* TODO: fix the tactic *)  Admitted.


Definition strlen_C_exec_corr_l :
  forall (m : Mem.mem) (b : block) (ofs : Z) (e : env) (le : temp_env) (z : Z),
    le!_s = Some (Vptr b (Ptrofs.repr ofs)) -> 
    (exists le', le'!_i = Some (Vint (Int.repr z)) /\ 
                bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr z),tuint))))
           -> strlen_C m b ofs = Some (z,m).
Proof.
  intros.
  repeat destruct H0.
  inversion H1.
  solve_by_inverts 5%nat. solve_by_inverts 15%nat. 
  unfold strlen_C.  unfold strlen_fun_C. unfold Mem.loadv in H9.
  Admitted.
              
(* Examples of running a program: to see what assumptions need in the proof, experiments *)

Parameter hi : Z.
Definition init_mem := fst (Mem.alloc Mem.empty 0 hi).
Definition b' := snd (Mem.alloc Mem.empty 0 hi).
Parameter ofs' : Z.
Hypothesis ofs_le_hi : ofs' < hi.

(* Example 1 : output on empty string is correct *)

Definition init_mem1 := 
  Mem.store Mint8signed init_mem b' ofs' (Vint (Int.repr 0)).


Lemma example_comp : forall m le e, init_mem1 = Some m ->
                             le!_s = Some (Vptr b' (Ptrofs.repr ofs')) ->
                             exists le', bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr 0),tuint))).
Proof.
  intros.
  exists (Maps.PTree.set _i (Vint (Int.repr 0)) le).
  repeat econstructor.
    + rewrite PTree.gso. apply H0. eapply Pos.succ_discr. 
    + apply Maps.PTree.gss.
    + econstructor.
    + unfold init_mem1 in H. simpl. rewrite (Mem.load_store_same  Mint8signed init_mem b' _ (Vint (Int.repr 0))). constructor. rewrite <- ptr_ofs_eq. assumption.
    + econstructor.
    + econstructor.
    + econstructor.
    + apply Maps.PTree.gss.
Qed. 

(* Running on a non-empty string: TODO prove the loop  *)

Definition init_mem0 := fst (Mem.alloc Mem.empty 0 hi).
Definition init_mem2 := Mem.store Mint8signed init_mem0 b' ofs' (Vint (Int.repr 1)).
Definition init_mem3 := match init_mem2 with
                        | None => None
                        | Some m => Mem.store Mint8signed m b' (ofs'+1) (Vint (Int.repr 0))
                        end.

Lemma example_comp2 : forall m le e,
                          init_mem2 = Some m ->
                          init_mem3 = Some m -> 
                          le!_s = Some (Vptr b' (Ptrofs.repr ofs')) ->
                          exists le', bigStepExec ge e le m f_strlen.(fn_body) t le' m (Out_return (Some (Vint (Int.repr 1),tuint))).
Proof.
  intros.
  exists (Maps.PTree.set _i (Vint (Int.repr 1)) le).
  repeat econstructor.
    + rewrite PTree.gso. apply H1. eapply Pos.succ_discr. 
    + apply Maps.PTree.gss.
    + econstructor.
    + unfold init_mem3 in H0. rewrite H in H0. simpl. rewrite <- ptr_ofs_eq.
      unfold init_mem2 in H. rewrite <- H in H0. rewrite -> (Mem.load_store_same Mint8signed init_mem0 b' ofs' (Vint (Int.repr 1))). econstructor. assumption.
    + econstructor.      
    + econstructor.
    + Print exec_stmt. admit. 
Admitted.

     
(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)



(* 

                                                
   
      
  
Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall z ge e m b ofs outp le,
      1 <= Z.of_nat outp + 1 < Ptrofs.modulus ->
      0 < z ->
      ofs + Z.of_nat outp < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      1 <= Z.of_nat outp < Ptrofs.modulus ->
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
      le!_output = Some (Vint_of_nat outp) ->
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr z)) ->
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\
               (le'!_output) = Some (Vint_of_nat (outp + 1)).

Proof.
  intro Arch.
  intros z ge e m b ofs outp le.
  intro P.
  intro Z.
  intro S.
  intros.
  repeat eexists.
  Print exec_stmt.
  - eapply exec_Sloop_loop.

    eapply exec_Sifthenelse. econstructor. econstructor. econstructor.
    econstructor.
    econstructor.
    apply H1.
    econstructor.
    apply H2. econstructor. econstructor. econstructor. simpl.
    assert ( (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr (Z.of_nat outp)))))) = (ofs + (Z_of_nat outp)) ) as E1. 
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.  unfold Ptrofs.of_intu. unfold Ptrofs.of_int. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Zmod_small ; nia. }
    rewrite E1. apply H3.
    econstructor.
    econstructor. simpl.
    cut ((negb (Int.eq (Int.repr z) (Int.repr 0))) = true). intro aux. rewrite aux. simpl. econstructor. {  admit. }
    econstructor.
    econstructor.
    econstructor.
    econstructor. 
   
    econstructor.
    apply H2.
     econstructor.
     econstructor.
     eapply exec_Sloop_stop1. repeat econstructor. rewrite PTree.gso. apply H1. cbv. congruence. 
     apply PTree.gss. econstructor. simpl.

      assert ( 
    (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
          (Ptrofs.mul (Ptrofs.repr 1)
             (Ptrofs.of_intu (Int.add (Int.repr (Z.of_nat outp)) (Int.repr 1)))))) = (ofs + (Z_of_nat outp + 1)) ) as E1. 
    { pose (Ptrofs.modulus_eq32 Arch).
      rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.  unfold Ptrofs.of_intu. unfold Ptrofs.of_int. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Zmod_small; unfold Int.add; repeat rewrite Int.unsigned_repr_eq ;  repeat rewrite Zmod_small;  admit. } 
    rewrite E1. (* Mem.load Mint8signed m b (ofs + (Z.of_nat outp + 1)) = Some ?v10 *)

                                                                       

Admitted.

 *)
