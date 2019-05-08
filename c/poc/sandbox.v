Lemma strlen_loop_continue_correct : Archi.ptr64 = false -> forall z ge e m b ofs outp le,
      
      1 <= Z.of_nat (S outp) < Ptrofs.modulus ->
      0 < z < Int.modulus ->
      ofs + Z.of_nat ( S outp ) < Ptrofs.modulus ->
      0 < ofs < Ptrofs.modulus ->
      0 <= Z.of_nat outp < Ptrofs.modulus ->
      
      le!_input = Some (Vptr b (Ptrofs.repr (ofs + (Z.of_nat outp)))) ->
      le!_output = Some (VintN outp) ->
      
      Mem.load Mint8signed m b (ofs + (Z_of_nat outp)) = Some (Vint (Int.repr z)) ->
      
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m Out_normal /\ (le'!_output) = Some (VintN (S outp)).
Proof.
  induction outp.
  intros.
  repeat eexists.
  - loop.  repeat econstructor; repeat gso_assumption. repeat econstructor. simpl.
     replace  (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr (ofs + 0))
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with (ofs + Z.of_nat 0). apply H7. { pose (Ptrofs.modulus_eq32 H). rewrite Ptrofs.mul_commut. rewrite Ptrofs.mul_one. ptrofs_compute_add_mul. all: nia. }
   econstructor. simpl. replace  (negb (Int.eq (Int.repr z) (Int.repr 0))) with true.
    econstructor. { admit. } 
    repeat econstructor. econstructor.
    repeat econstructor. gso_assumption.
    repeat econstructor.
    assert (exists t, exec_stmt ge e (PTree.set _output (Vint (Int.add (Int.repr (Z.of_nat 0)) (Int.repr 1))) le)
    m
    (Sloop
       (Sifthenelse
          (Ebinop One
             (Ederef
                (Ebinop Oadd (Etempvar _input (tptr tschar)) (Etempvar _output tuint)
                   (tptr tschar)) tschar) (Econst_int (Int.repr 0) tint) tint) Sskip Sbreak)
       (Sset _output (Ebinop Oadd (Etempvar _output tuint) (Econst_int (Int.repr 1) tint) tuint)))
    t (PTree.set _output (Vint (Int.add (Int.repr (Z.of_nat 0)) (Int.repr 1))) le) m Out_normal ).
    
    fold f_strlen_loop. apply (strlen_loop_break_correct2 H _  _ _ b ofs (S O) _) ; try nia ; try assumption.  gso_assumption.
  admit. admit. apply gss.
Admitted.


Lemma strlen_non_empty_corr : (* with this assumption Ptrofs.modulus = Int.modulus, ptherwise Ptrofs.modulus > Int.modulus *)
  Archi.ptr64 = false ->
  forall ge e m b ofs le len,
                       
               (* Preconditions on the length of the string and valid offset *)
    0 < ofs < Ptrofs.modulus ->
    Z_of_nat (S len) < Int.modulus ->
    ofs + Z_of_nat (S len) < Ptrofs.modulus ->
                       
                       (* Initialize local variables *)
    le!_input = Some (Vptr b (Ptrofs.repr ofs)) ->
    le!_output = Some (VintZ 0) ->

                       
       (* Precondition: reading C string from memory *)
    forall i z, (i < S len)%nat ->
           Mem.load chunk m b (ofs + Z.of_nat i) = Some (VintN (S z)) ->
           Mem.load chunk m b (ofs + Z.of_nat (S len)) = Some (VintN O) ->
           
      exists t le', exec_stmt ge e le m f_strlen.(fn_body) t le' m (Out_return (Some ((VintN (S len)),tuint))) /\
                    (le'!_output) = Some (VintN (S len)).
Proof.
  induction len.
  - (* Base case *) intro L. intros.
     repeat eexists.
 
  -- seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl. replace (Ptrofs.unsigned
                                               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. assert (i = O). omega. rewrite H7 in H5. simpl in H5. replace (ofs) with (ofs + 0) by lia. apply H5.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: nia. } repeat econstructor. simpl. replace  (negb
          (Int.eq (Int.repr (Z.pos (Pos.of_succ_nat z)))
                  (Int.repr 0))) with true.  repeat econstructor. { admit.  } econstructor. repeat econstructor. repeat econstructor. apply gss. repeat econstructor.

        (* exit loop *)
        eapply exec_Sloop_stop1. (* break from the loop *)
        repeat econstructor.  rewrite gso; repeat gso_assumption.  eapply gss.
        repeat econstructor. simpl.
        replace (Ptrofs.unsigned
       (Ptrofs.add (Ptrofs.repr ofs)
                   (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.add (Int.repr 0) (Int.repr 1)))))) with (ofs + 1). apply H6.  { pose (Ptrofs.modulus_eq32 H). ptrofs_compute_add_mul. all: admit. }
                                                                                                                                  repeat econstructor. simpl. repeat econstructor. econstructor. econstructor.
    + (* return statement *)
      repeat econstructor. eapply gss.
      -- eapply gss.

   -. intros. repeat eexists. -- seq1.
    + seq1.
      * sset. (* evaluate expression *) repeat econstructor.
      * (* loop 1 *)
        loop. repeat econstructor. repeat gso_assumption. eapply gss.        repeat econstructor. simpl.
        induction i.
        replace (Ptrofs.unsigned
                                               (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr 0))))) with ofs. simpl in H6. replace ofs with  (ofs + 0) by lia. apply H6. { admit. } apply IHi. omega.
                                                                                                                                  
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


(* TODO : fix this *)
Inductive C_string (m : Mem.mem) (b : block) (ofs : Z) (len : nat) :=
  is_C_string : forall n i, (0 < Z.of_nat n < Int.modulus) ->
                        (0 <= i < len)%nat ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat i) = Some (VintN n) ->
                        Mem.load Mint8signed m b (ofs + Z_of_nat len) = Some (VintZ 0) ->
                        C_string m b ofs len.


Lemma strlen_correct_with_C_string : Archi.ptr64 = false -> forall ge e m b ofs le len,
      
      (0 <= Z_of_nat len < Int.modulus ) -> (* len is within bounds *)
      0 < ofs < Ptrofs.modulus -> 
      (ofs + Z_of_nat len) < Ptrofs.modulus ->  (* the offsets are valid *)
  
      le!_input = Some (Vptr b (Ptrofs.repr ofs)) -> (* input is an address [b,ofs] *) 
      le!_output = Some (VintZ 0) -> (* we start from 0 *)
      
      C_string m b ofs len -> (* [b,ofs] points to a string of length len in memory m *)
      
      exists t le', exec_stmt ge e le m f_strlen_loop t le' m (Out_return (Some (VintN len, tuint))) /\
               (le'!_output) = Some (VintN len).
(* the C light expression evaluates to outcome Out_return (Some VintN len) and output is set to len *)
Admitted.
