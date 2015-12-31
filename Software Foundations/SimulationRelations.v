(**
   Formalizing Simulation Relations in Coq by Elaheh Ghassabani
   University of Minnesota
**)

Require Export SfLib.
Require Import ClassicalChoice.
(**
  Semantically, Atoms are variables like a b c, and so on.
  Atomic propositions state simple facts about a state. 
  States are distinguished by the fact that which atoms they have or
  which atoms they satisfy. 
  So, we can model states as a function atom -> bool. 
**)


(** Atomic Proposition : a single atom **)
Definition atom := Type.
(**
  With this assumption that we have a defined set of atoms, each state
  maps an atom in the set to true or false.
**)
Definition state := atom -> bool.


(*******  Formulating Transition Systems *******)
Definition initial_states := state -> Prop. 
Definition transition_relation := state -> state -> Prop.
(**
   We think of Atoms as a set of atomic propositions: if [A : Atoms], 
   [A] includes a set of atomic propositions.
**)
Definition Atoms := atom -> Prop.
 
(** Transition System **)

Definition complete_tr (tr: transition_relation) : Prop :=
  forall (s : state) , exists (s' : state) , tr s s'.

Inductive TS : Type :=
  trans_sys (ap : Atoms) (i : initial_states) (tr : transition_relation):
         complete_tr (tr) -> (exists s, i s)  -> TS.

Definition Ap (ts : TS) : Atoms := 
  match ts with
  | trans_sys x _ _ _ _ => x
  end.
Definition Init (ts : TS) : initial_states := 
   match ts with
  | trans_sys _ y _ _ _ => y
  end.
Definition TRL (ts : TS) : transition_relation := 
   match ts with
  | trans_sys _ _ z _  _ => z
  end.
   

(*Notation "( x , y , z )" := (trans_sys x y z).*)


(****************  LTL Syntax ****************)
Inductive LTL_exp : Type :=
  | TRUE    : LTL_exp
  | FALSE   : LTL_exp
  | AP      : atom -> LTL_exp
  | AND     : LTL_exp -> LTL_exp -> LTL_exp
  | IMP     : LTL_exp -> LTL_exp -> LTL_exp
  | OR      : LTL_exp -> LTL_exp -> LTL_exp
  | NOT     : LTL_exp -> LTL_exp
  | F       : LTL_exp -> LTL_exp
  | G       : LTL_exp -> LTL_exp
  | U       : LTL_exp -> LTL_exp -> LTL_exp
  | X       : LTL_exp -> LTL_exp
  | W       : LTL_exp -> LTL_exp -> LTL_exp.



(****************  Trace ****************)
(*  
  a trace can be modeled as a sequence of states. So, it has to show
  the order of states. Thus, we can model a Trace as a map from nat to 
  state.
*)
Definition Trace := nat -> state. 


(* returns trace tn...*)
Definition suffix (t : Trace) (n : nat) : Trace := fun i => t (i + n). 
Check suffix.
(*  
   Trace -> nat -> Trace : [suffix returns a Trace]
*)


Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* It says:
     (fun i : nat => t (i + m + n)) = (fun i : nat => t (i + (m + n))
*)
Theorem plus_assoc_in_trace : forall (t : Trace) (n m : nat),
       suffix (suffix t n) m = suffix t (m + n).
Proof.
     intros. apply functional_extensionality.
     intros. unfold suffix. rewrite plus_assoc.
     reflexivity.
Qed.


Theorem subtrace0 : forall (n : nat) (t : Trace),
    suffix t n = suffix (suffix t n) 0.
Proof.
     intros. apply functional_extensionality.
     intros. unfold suffix. 
     rewrite <- plus_assoc. 
     rewrite plus_O_n. reflexivity.
Qed.

(* a sub-case of subtrace0 *)
Lemma t0 : forall(t : Trace), (suffix t 0)  = t.
Proof.
     intros. rewrite subtrace0. 
     unfold suffix.
     apply functional_extensionality.
     intros. 
     repeat (rewrite <- plus_assoc; rewrite <- plus_comm; rewrite plus_O_n). 
     reflexivity.
Qed.


(***********************************************************************************************************)
(** LTL Semantics **** OPERATORS **)
(***********************************************************************************************************)
Fixpoint LTL_sat (prop : LTL_exp) (t : Trace) := 
     match prop with 
     | TRUE    => True
     | FALSE   => False
     | AP ap   => (t 0) ap = true 
     | AND p q => (LTL_sat p t) /\ (LTL_sat q t)
     | IMP p q => (LTL_sat p t) -> (LTL_sat q t) 
     | OR  p q => (LTL_sat p t) \/ (LTL_sat q t)
     | NOT   p => not(LTL_sat p t)  
     | U   p q => exists n, LTL_sat q (suffix t n) /\ 
                  (forall (m : nat) (c: m < n), LTL_sat p (suffix t m))
     | F     p => exists n, LTL_sat p (suffix t n)
     | G     p => forall (n : nat) , LTL_sat p (suffix t n)
     | X     p => LTL_sat p (suffix t 1)
     | W   p q => (exists n, LTL_sat q (suffix t n) /\ 
                  (forall (m : nat) (c: m < n), LTL_sat p (suffix t m))) \/ 
                  (forall (m : nat), LTL_sat p (suffix t m)) 
     end.
(**********************************************************************************************************)

Axiom not_not : forall (p : LTL_exp) (t : Trace),
       ~~ LTL_sat p t <-> LTL_sat p t. 


          	
Definition state_equiv (apA : Atoms)(sa sc : state) : Prop :=
             forall p, apA p -> sa p = sc p.



Definition trace_of_ts (t : Trace) (ts : TS) := 
             (exists s, (Init ts) s /\ state_equiv (Ap ts) s (t 0)) /\
             (forall (i : nat), exists s s', (TRL ts) s s' /\
                      state_equiv (Ap ts) s (t i) /\ 
                      state_equiv (Ap ts) s' (t (i+1))).

Definition subtrace_of_ts (t : Trace) (ts : TS) (max: nat) := 
             (exists s, (Init ts) s /\ state_equiv (Ap ts) s (t 0)) /\
             (forall (i : nat), (i <= max) -> 
                 exists s s', (TRL ts) s s' /\
                      state_equiv (Ap ts) s (t i) /\ 
                      state_equiv (Ap ts) s' (t (i+1))).



Theorem s_has_trace :  forall T, complete_tr T-> 
             forall s, exists t, t 0 = s /\ 
             forall n, T (t n) (t (S n)).
Proof.
    intros.
    apply choice in H as [f Hf].
    exists (fix p n := match n with
                   | 0 => s
                   | S n' => f (p n')
                   end).
    auto.
Qed.





Lemma state_equiv_trans : forall (sa sc s' : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv apA sa sc -> state_equiv apC sc s' ->
       state_equiv apA sa s'.
Proof. 
   intros.
   unfold state_equiv in H0.
   unfold state_equiv in H1.
   unfold state_equiv.
   intros.
   assert (apA p) by assumption.
   apply H0 in H2.
   apply H in H3.
   apply H1 in H3.
   rewrite <- H2 in H3.
   assumption.
Qed.

Lemma state_equiv_sub : forall (sa sc : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv apC sa sc -> state_equiv apA sa sc.
Proof.
   intros.
   unfold state_equiv in H0.
   unfold state_equiv.
   intros.
   apply H in H1. apply H0 in H1. assumption.
Qed.

Lemma state_equiv_comm : forall (s s' : state) (ap : Atoms),
      state_equiv ap s s'  <-> state_equiv ap s' s.
Proof.
    intros. split; unfold state_equiv; intros;
    apply H in H0; rewrite H0; reflexivity.
Qed. 


Lemma state_equiv_imp : forall (sa sc s : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv apA sa s  /\ state_equiv apC sc s  ->
       state_equiv apA sa sc.
Proof.
    intros. unfold state_equiv. intros.
    unfold state_equiv in H0. inversion H0. clear H0.
    assert (apA p) by assumption.
    apply H2 in H1. 
    apply H in H0. apply H3 in H0. rewrite <- H1 in H0.
    symmetry. assumption.
Qed.

Lemma state_equiv_red : forall (sa sc s : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv apC sa s  /\ state_equiv apC sc s -> 
       state_equiv apA sa sc.
Proof.
   intros.
   unfold state_equiv in H0.
   unfold state_equiv.
   intros.
   inversion H0.
   apply H in H1. 
   assert (apC p) by assumption. 
   apply H2 in H1.
   apply H3 in H4. rewrite <- H4 in H1.
   assumption.
Qed.


Lemma state_equiv_imp2 : forall (sa sc s : state) (ap : Atoms),
       state_equiv ap sa s  /\ state_equiv ap sc s -> 
       state_equiv ap sa sc.
Proof.
    unfold state_equiv.
    intros. inversion H.
    assert (ap p) by apply H0.
    apply H1 in H0. apply H2 in H3.
    rewrite <- H3 in H0. assumption.
Qed.
      
    
(**----------------------------------------------------------------------------------***)

(** 
    The meaning of the notion that transition system [ts] satisfies 
    LTL property [p]: 
 **)
Definition TS_sat_LTLp (prop : LTL_exp)(ts : TS) :=
       (forall (trc : Trace), trace_of_ts trc ts ->  LTL_sat prop trc).


(* 
   Definition of Simulation Relations
*)

Definition SR (apA : Atoms)(sa sc : state) :=  state_equiv apA sa sc.

(*----------------------------------------------*)

(* Make this explicit: this is Strong Simulation *)

Definition Strong_SimRel (TSa TSc : TS) := 
        (forall (p : atom), (Ap TSa) p -> (Ap TSc) p) /\
	(forall (sc : state), (Init TSc) sc -> exists sa, 
                (Init TSa) sa /\ SR (Ap TSa) sa sc) /\
        (forall (sa sc sc' : state),(SR (Ap TSa) sa sc) /\ (TRL TSc) sc sc' -> 
        (exists sa', (TRL TSa) sa sa' /\  SR (Ap TSa) sa' sc')).

(*
  If [A] simulate5 [C], every trace of [C] has an equivalent
  trace in [A].
*)
Lemma trace_inclusion_strong : forall (TSa TSc : TS),
           Strong_SimRel TSa TSc ->
          (forall (t : Trace), trace_of_ts t TSc ->
           trace_of_ts t TSa).
Proof.
     intros. destruct TSa as [APa INITa TRa] eqn:A.
     destruct TSc as [APc INITc TRc] eqn:C.
     unfold trace_of_ts.
     unfold trace_of_ts in H0. 
     inversion H. clear H.
     inversion H2. clear H2.
     inversion H0.
     clear H0. inversion H2. clear H2.
     inversion H0.
     apply H in H2. inversion H2. 
     split. 
     Case "left" .
       exists x0. split.
       SCase "left".
          apply H6.
       SCase "right".
         apply state_equiv_trans with (sc := x) (apC := APc).
         assumption. apply H6. assumption.
    Case "right".
      intros.
      induction i.
      SCase "i is O".
        exists x0.
        assert (exists s s', TRc s s' /\  state_equiv APc s (t 0) /\
                               state_equiv APc s' (t 1)) by apply H4.
        inversion H7. inversion H8; clear H8 H7.
        inversion H9. inversion H8; clear H8 H9.
        assert (SR APa x0 x1  /\ TRc x1 x2 ->
                exists s, TRa x0 s /\ SR APa s x2) by apply H3; clear H3.
        assert (TC: TRc x1 x2) by assumption.
        inversion H0.
        assert (SR APa x0 x1).
        SSCase "Proof_of_assertion".
            inversion H6. 
            assert (state_equiv APa x0 (t 0)).
            SSSCase "Proof_of_assertion".
                apply state_equiv_trans with (apC := APc) 
                  (sa := x0) (sc := x) (s' := (t 0));
                assumption. 
            apply state_equiv_imp with (apC := APc) 
                  (sa := x0) (sc := x1) (s := (t 0)). assumption.
            split; assumption.
        assert (SR APa x0 x1 /\ TRc x1 x2) by (split; assumption). 
        apply H8 in H13. clear H8. inversion H13; clear H13.
        exists x3. split. 
        SSCase "left". 
          apply H8. 
        SSCase "right".
          split.
          SSSCase "left".
             apply state_equiv_trans with (sa := x0) (apA := APa)
                     (sc := x1) (s' := (t 0)) (apC := APc)  in H10;
             try (apply H3 in H9); assumption.
          SSSCase "right".
             rewrite plus_O_n. 
             apply state_equiv_imp with (sa := x3) (apA := APa)
                     (s := x2) (sc := (t 1)) (apC := APc).
             assumption. split. apply H8. apply state_equiv_comm. assumption.

    SCase "i is S i'".
       inversion IHi;  inversion H7; clear IHi H7.
       inversion H8. inversion H9; clear H9.
       exists x2. 
       assert (exists s s', TRc s s' /\ state_equiv APc s (t (S i)) /\
               state_equiv APc s' (t (S i + 1))) by apply H4; clear H4.
       inversion H9. inversion H4; clear H9 H4.
       inversion H12; clear H12.
       assert (SR APa x2 x3 /\ TRc x3 x4 ->
               exists s, TRa x2 s /\ SR APa s x4) by apply H3; clear H3.
       assert (TCx : TRc x3 x4) by assumption.
       assert (SR APa x2 x3).
       SSCase "Proof_of_assertion".
            inversion H6. 
            apply state_equiv_imp with (apC := APc) 
                  (sa := x2) (sc := x3) (s := (t (S i))). assumption.
            split. replace (S i) with (i + 1). assumption.
            apply plus_comm. apply H9.
       assert (SR APa x2 x3  /\ TRc x3 x4) by (split; assumption).        
       apply H12 in H13. clear H12.
       inversion H13; clear H13.
       exists x5. split.
       SSCase "left".
          apply H12.
       SSCase "right". 
          split.
          SSSCase "left".
             replace (S i) with (i + 1); try (apply H7);
             rewrite plus_comm.
          SSCase "right".
             inversion H12.
             rewrite plus_comm. apply H11.
             reflexivity.
             apply state_equiv_trans with (sa := x5) (apA := APa)
                     (sc := x4) (s' := (t (S i + 1))) (apC := APc);
             try (assumption). apply H12.  apply H9.
Qed.


(*
  if [A] simulates [C], 
  every LTL properties satisfied by [A] is also satisfied by [C].
*)     
Theorem strong_simulation_relations : 
            forall (prop : LTL_exp)(TSa TSc: TS), 
            Strong_SimRel TSa TSc ->  
            TS_sat_LTLp prop TSa -> 
            TS_sat_LTLp prop TSc.
Proof.
     intros.
     unfold TS_sat_LTLp. intros.
     unfold TS_sat_LTLp in H1.
     destruct TSa as [APa INITa TRa] eqn:A.
     destruct TSc as [APc INITc TRc] eqn:C.
     apply trace_inclusion_strong with (t := trc) in H;
     try (assumption). 
     apply H0; try (assumption).
Qed.

(*----------------------------------------------*)

Definition reachable (s : state) (ts : TS) := 
    exists t i, trace_of_ts t ts /\  
                          state_equiv (Ap ts) s (t i).


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Lemma ev_od_tf : forall n, evenb n = true -> evenb (S n) = false.
Proof. 
    intros. induction n as [| n'].
    reflexivity.
    destruct (evenb (S (S n'))) eqn: HD.
    inversion HD.
    assert (HF: evenb n' = true) by apply H1.
    apply IHn' in H1. rewrite H in H1. inversion H1.
    reflexivity.
Qed.
Lemma ev_od_ft : forall n, evenb n = false -> evenb (S n) = true.
Proof. 
    intros. induction n as [| n'].
    inversion H.
    destruct (evenb (S (S n'))) eqn: HD.
    inversion HD.
    reflexivity.
    simpl in HD.
    assert (HF: evenb n' = false) by apply HD.
    apply IHn' in HF. rewrite H in HF. inversion HF.
Qed.    



Lemma trace_is_subtrace : forall t s ts i,
              trace_of_ts t ts -> 
              state_equiv (Ap ts) s (t i) ->
              subtrace_of_ts t ts i.
Proof.
   intros.
   unfold subtrace_of_ts.
   split.
   apply H.
   intros.
   apply H.
Qed.


Lemma le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof. 
  intros.
  generalize dependent n.
  induction m.
  Case "m is O". 
    intros.
    inversion H. reflexivity.
  Case "m is S m'".
    destruct n.
    SCase "n is O".
       reflexivity.
    SCase "n is S n'".
       simpl. intros.
       inversion H. 
       assert (m <= m -> ble_nat m m = true) by apply IHm.
       apply H0. rewrite -> H1 in H. 
       omega.
       assert (n <= m -> ble_nat n m = true) by apply IHm.
       apply H2. omega.
Qed.


Theorem le_ble_nat2 : forall n m,
   (n > m) -> ble_nat n m = false.
Proof.
   intros.
  generalize dependent n.
  induction m.
  Case "m is O". 
    intros.
    inversion H. reflexivity.
    reflexivity.
  Case "m is S m'".
    destruct n.
    SCase "n is O".
       intros. inversion H.
    SCase "n is S n'".
       simpl. intros.
       simpl in H. apply gt_S_n in H.
       apply IHm. assumption.
Qed.

               
Lemma map_trace :  forall t t' ts max,
              subtrace_of_ts t ts max -> 
              state_equiv (Ap ts) (t' 0) (t max) -> 
              (forall n, exists x x', (TRL ts) x x' /\
                      state_equiv (Ap ts) x (t' n) /\
                      state_equiv (Ap ts) x' (t' (S n))) ->
              exists T, trace_of_ts T ts /\
              forall j, j <= max -> t j = T j /\
              forall k, k > max -> t' (k - max) = T k.
Proof.
   intros.
   destruct ts as [ap ini tr] eqn:tsd.  
   exists (fun n : nat => match n with
                   | 0       => t n
                   | S n'    => match ble_nat n max with 
                             | true  =>  t n
                             | false =>  t' (n - max)
                             end
                   end).
   unfold subtrace_of_ts in H.
   split. 
   Case "left".
      unfold trace_of_ts. simpl. split.
      SCase "left".
         apply H.
      SCase "right".
         induction H.
         generalize dependent max.
         induction i as [ |i'].
         SSCase "i is O".
           simpl in H1. 
           simpl. destruct max. 
           SSSCase "left".
               assert (exists x x', tr x x' /\ state_equiv ap x (t' 0) /\
                        state_equiv ap x' (t' 1)) by apply H1.
               repeat (induction H3). 
               exists x. exists x0.
               split.  apply H3. split.
               apply state_equiv_imp2 with (s := (t' 0)).
               split. apply H4. 
               apply state_equiv_comm. assumption. apply H4. 
           SSSCase "right".
               simpl in H2.
               apply H2. omega.
       SSCase "i is S i'".
           simpl.  destruct max eqn:M; simpl in IHi'.
           SSSCase "left".
               replace (i' + 1) with (S i').
               apply H1. omega.
           SSSCase "right".
               destruct (ble_nat i' n) eqn:Heq1.
               destruct (ble_nat (i' + 1) n) eqn:Heq2.
               SSSSCase "both if are ture".
                     apply ble_nat_true in Heq1.
                     apply H2. omega.
               SSSSCase "true&false".
                     apply ble_nat_true in Heq1. 
                     apply ble_nat_false in Heq2.
                     unfold not in Heq2.
                     destruct i' eqn: I'. simpl in IHi'.
                     assert (n = 0). omega.
                     rewrite H3. simpl. 
                     rewrite H3 in H0.
                     assert (exists x x', tr x x' /\ state_equiv ap x (t' 0) /\
                        state_equiv ap x' (t' 1)) by apply H1.
                     repeat (induction H4). 
                     exists x. exists x0.
                     split.  apply H4. split.
                     apply state_equiv_imp2 with (s := (t' 0)).
                     split. apply H5. 
                     apply state_equiv_comm. assumption. apply H5.  
                     assert (n0 <= n). omega. 
                     assert (n0 + 1 <= n). omega.
                     subst. assert (S n0 +1 - n = 1).  omega.
                     assert (S (S n0) = S n). omega.
                     rewrite H5. rewrite H6.
                     assert (exists x x', tr x x' /\ state_equiv ap x (t' 0) /\
                        state_equiv ap x' (t' 1)) by apply H1.
                     repeat (induction H7). 
                     exists x. exists x0.
                     split.  apply H7. split.
                     apply state_equiv_imp2 with (s := (t' 0)).
                     split. apply H8. 
                     apply state_equiv_comm. assumption. apply H8. 
              destruct (ble_nat (i' + 1) n) eqn:Heq2.
              SSSSCase "false&true".
                     apply ble_nat_false in Heq1. 
                     apply ble_nat_true in Heq2.
                     unfold not in Heq1.
                     assert (i' > n). omega.
                     rewrite plus_comm in Heq2. 
                     simpl in Heq2. 
                     assert (False). apply Heq1. omega.
                     inversion H4.
              SSSSCase "false&false".
                     replace (i' + 1 - n) with (S (i' - n)).
                     apply H1. rewrite plus_comm.  
                     rewrite minus_Sn_m. reflexivity.
                     apply ble_nat_false in Heq1. 
                     apply ble_nat_false in Heq2.
                     apply NPeano.Nat.nlt_ge. omega.
     SCase "left".
         split. destruct j. reflexivity.
         replace (ble_nat (S j) max) with true. reflexivity.
         symmetry. 
         apply le_ble_nat. assumption.
         intros.
         assert (k > O). omega. simpl. 
         inversion H4. simpl. 
         assert (max = O). omega. inversion H6. reflexivity.
         replace (ble_nat (S m) max) with false. reflexivity.
         symmetry. apply le_ble_nat2. omega.
Qed.


              
Lemma extend_subtrace : forall t ts max,
              subtrace_of_ts t ts max -> 
              exists t', trace_of_ts t' ts /\
              forall j, j <= max -> t j = t' j.
Proof.
   intros.
   destruct ts as [ap ini tr] eqn:tsd.  
   assert (Hc: complete_tr tr) by apply c.
   apply s_has_trace with (s := (t max)) in Hc.
   inversion Hc.
   exists (fun n : nat => match n with
                   | 0       => t n
                   | S n'    => match ble_nat n max with 
                             | true  =>  t n
                             | false =>  x (n - max) 
                             end
                   end). 
    unfold subtrace_of_ts in H.
   split. 
   Case "left".
      unfold trace_of_ts. simpl. split.
      SCase "left".
         apply H.
      SCase "right".
         induction H.
         generalize dependent max.
         induction i as [ |i'].
         SSCase "i is O".
           simpl in H1. 
           simpl. destruct max. 
           SSSCase "left".
               induction H0. rewrite <- H0.
               exists (x 0). exists (x 1).
               split. apply H2.
               unfold state_equiv; split; reflexivity.
           SSSCase "right".
               apply H1. apply le_O_n.
       SSCase "i is S i'".
           simpl.  destruct max eqn:M; simpl in IHi'.
           SSSCase "left".
               exists (x (S i')). exists (x (S (i' + 1))).
               split. 
               replace (i' + 1) with (S i'). apply H0.
               rewrite plus_comm. reflexivity. 
               unfold state_equiv; split; reflexivity.
           SSSCase "right".
               destruct (ble_nat i' n) eqn:Heq1.
               destruct (ble_nat (i' + 1) n) eqn:Heq2.
               SSSSCase "both if are ture".
                     apply ble_nat_true in Heq1.
                     apply H1. omega.
               SSSSCase "true&false".
                     apply ble_nat_true in Heq1. 
                     apply ble_nat_false in Heq2.
                     unfold not in Heq2.
                     destruct i' eqn: I'. simpl in IHi'.
                     assert (n = 0). omega.
                     rewrite H2. simpl. 
                     rewrite H2 in H0. induction H0. rewrite <- H0.
                     exists (x 0). exists (x 1).
                     split. apply H3.
                     unfold state_equiv; split; reflexivity.
                     assert (n0 <= n). omega. 
                     assert (n0 + 1 <= n). omega.
                     subst. assert (S n0 +1 - n = 1).  omega.
                     assert (S (S n0) = S n). omega.
                     rewrite H5. rewrite H4.
                     induction H0. rewrite <- H0.
                     exists (x 0). exists (x 1). 
                     split. apply H6.
                     unfold state_equiv; split;  reflexivity.
              destruct (ble_nat (i' + 1) n) eqn:Heq2.
              SSSSCase "false&true".
                     apply ble_nat_false in Heq1. 
                     apply ble_nat_true in Heq2.
                     unfold not in Heq1.
                     assert (i' > n). omega.
                     rewrite plus_comm in Heq2. 
                     simpl in Heq2. 
                     assert (False). apply Heq1. omega.
                     inversion H3.
              SSSSCase "false&false".
                     exists (x (i' -n)). exists (x (i' + 1 - n)).
                     split.
                     replace (i' +1 - n) with (S (i' - n)).
                     apply H0. 
                     rewrite plus_comm. 
                     rewrite minus_Sn_m. reflexivity.
                     apply ble_nat_false in Heq1. 
                     apply ble_nat_false in Heq2.
                     apply NPeano.Nat.nlt_ge. omega.
                     unfold state_equiv; split; intros; reflexivity.
     SCase "left".
         intros.
         destruct j as [| j']. reflexivity.
         replace (ble_nat (S j') max) with true. reflexivity.
         symmetry. 
         apply le_ble_nat. assumption.
Qed.

Lemma s_s'_has_trace : forall s s' tr ap,
                       complete_tr tr /\ tr s s' ->
                       (exists (t : Trace),
                        state_equiv ap s (t 0) /\ state_equiv ap s' (t 1) /\
                        forall k, exists x x', tr x x' /\
                        state_equiv ap x (t k) /\ state_equiv ap x' (t (S k))).
Proof.
    intros. induction H.
    apply choice in H as [f Hf].
    exists (fix p n := match n with
                   | 0    => s
                   | 1    => s'
                   | S n' => f (p n')
                   end).
    split. 
    unfold state_equiv; reflexivity. split. 
    unfold state_equiv; reflexivity.
    destruct k as [| k'].
    exists s. exists s'.
    split.
    apply H0.
    split; unfold state_equiv; reflexivity.
    simpl. 
    exists (match k' with 
              | 0 => s'
              | S _ =>
                 f ((fix p (n0 : nat) : state :=
                      match n0 with
                      | 0 => s
                      | 1 => s'
                      | S (S _ as n') => f (p n')
                      end) k')
             end). 
     exists (f (match k' with 
              | 0 => s'
              | S _ =>
                 f ((fix p (n0 : nat) : state :=
                      match n0 with
                      | 0 => s
                      | 1 => s'
                      | S (S _ as n') => f (p n')
                      end) k')
             end)). 
    split. apply Hf.
    split; unfold state_equiv; reflexivity.
Qed.
 
Lemma tr_reachable : forall (ts : TS) (s s': state), 
                        reachable s ts /\ (TRL ts) s s'
                        -> reachable s' ts .
Proof.
   intros.
   assert (Hh: reachable s ts /\ (TRL ts) s s') by apply H. 
   induction H.
   induction H. induction H. induction H.
   destruct ts as [ap ini tr] eqn:tsd.
   assert (Hc: complete_tr tr) by apply c.
   apply trace_is_subtrace with (i := x0) (s := (x x0)) in H.
   assert (complete_tr tr /\ tr s s'). split; assumption.
   apply s_s'_has_trace with (s := s) (s' := s') (ap := ap) in H2.
   induction H2.
   apply map_trace  with (t' := x1) (max := x0) in H.
   unfold reachable.
   induction H. induction H. exists x2. exists (S x0).
   split. assumption.
   induction H3 with (j := x0).
   assert ((x1 1) = (x2 (S x0))).
   replace 1 with (S x0 - x0).
   apply H5. omega. omega. 
   rewrite <- H6.
   unfold state_equiv. intros. 
   induction H2. 
   induction H8. rewrite H8. reflexivity.
   assumption. reflexivity. 
   apply state_equiv_imp with (s := s) (apC := ap).
    intros. assumption. 
    split; apply state_equiv_comm. apply H2. assumption.
    apply H2.
    unfold state_equiv; reflexivity.
Qed. 




Lemma all_trace_states_reachable  : 
    (forall (t: Trace) (ts: TS) i, trace_of_ts t ts -> (reachable (t i) ts))  .
Proof.  
    intros. unfold reachable.
    exists t. exists i.
    split. assumption.
    unfold state_equiv.  intros. reflexivity.
Qed.

        
(* Here is the definition: note that we don't need to bring in the reachability of the 
   post states in the consequent, because we can immediately derive this using trans_reachable.

   I think this definition should not present any substantial difficulty in the trace
   inclusion statement, because of the lemma all_trace_states_reachable.
 *)    

Definition Weak_SimRel (TSa TSc : TS) := 
           (forall (p : atom), (Ap TSa) p -> (Ap TSc) p) /\
           (forall (sc : state), (Init TSc) sc -> exists sa, 
                     (Init TSa) sa /\ SR (Ap TSa) sa sc) /\
           (forall (sa sc sc' : state),
               (reachable sc TSc /\ (SR (Ap TSa) sa sc)
                   /\ (TRL TSc) sc sc' -> 
                  (exists sa', (TRL TSa) sa sa' /\ 
                   SR (Ap TSa) sa' sc'))). 
   


Lemma trace_inclusion_weak : forall (TSa TSc : TS),
           Weak_SimRel TSa TSc ->
          (forall (t : Trace), trace_of_ts t TSc ->
           trace_of_ts t TSa).
Proof.
    intros.
    unfold trace_of_ts.
    inversion H0.
    induction H. 
    destruct TSa as [APa Ia TRa] eqn:tsd.
    destruct TSc as [APc Ic TRc] eqn:tsd'.
    simpl. 
    simpl in H3. induction H3.
    split. 
    Case "left".
       induction H1. simpl in H1. induction H1.
       apply H3 in H1. induction H1.
       exists x0. split. apply H1.
       apply state_equiv_trans with (sc := x) (apC := APc).
       assumption. apply H1. apply H5.
    Case "right".
       induction i.
       SCase "i is O".
          simpl in H2.
          assert (exists s s', TRc s s' /\ state_equiv APc s (t 0) /\
                  state_equiv APc s' (t 1)) by apply H2. clear H2.
          induction H5. induction H2.
          assert (reachable x TSc).
          SSCase "Proof_of_assertion".
               unfold reachable.
               exists t. exists 0. split;
               rewrite tsd'. apply H0.
               simpl. apply H2.
          induction H1. simpl in H1.
          induction H1. apply H3 in H1.
          induction H1.
          assert (SR APa x2 x).
          SSCase "Proof_of_assertion".
               unfold SR.  
               assert (state_equiv APa x2 (t 0)).
               SSSCase "Proof_of_assertion".
                   induction H1.
                   unfold SR in H7.
                   apply state_equiv_trans with (sa := x2) (s' := (t 0)) (sc := x1) (apC := APc);
                   assumption.
               induction H2. induction H8.
               apply state_equiv_imp with (sa := x2) (sc := x) (s := (t 0)) (apC := APc).
               assumption. split; assumption.
               rewrite <- tsd' in H4.
           assert (reachable x TSc /\ SR APa x2  x /\ TRc x x0).
              split. assumption. split. assumption. apply H2.
           apply H4 in H8.
           induction H8.
           exists x2. exists x3.
           split. apply H8.
           induction H2. induction H9.
           split.
           apply state_equiv_trans with (sa := x2) (sc := x1) (s' := (t 0)) (apC := APc).
           assumption. apply H1. assumption.
           simpl. 
           apply state_equiv_trans with (sa := x3) (sc := x0) (s' := (t 1)) (apC := APc).
           assumption. apply H8. assumption.    
       SCase "i is S i".
           induction IHi. induction H5.
           inversion H5. induction H7.
           exists x0. 
           assert (exists s s', TRc s s' /\ state_equiv APc s (t (S i)) /\
                     state_equiv APc s' (t (S i + 1))) by apply H2; clear H2.
           induction H9. induction H2. induction H2.
           assert (reachable x1 TSc).
           SSCase "Proof_of_assertion".
               unfold reachable.
               exists t. exists (S i). split;
               rewrite tsd'. apply H0.
               simpl. apply H9.
           rewrite <- tsd' in H4.
           assert (reachable x1 TSc /\ SR APa x0 x1 /\ TRc x1 x2 ->
                    exists s, TRa x0 s /\ SR APa s x2) by apply H4.
           induction H11.
           exists x3.
           split. apply H11.
           split. replace (S i) with (i + 1). apply H8. omega.
           induction H11.
           unfold SR in H12. 
           apply state_equiv_trans with (sa := x3) (sc := x2) (s' := t (S i + 1)) (apC := APc).
           assumption. assumption. apply H9.
           split. assumption. split.
           unfold SR.
           apply state_equiv_imp with (sa := x0) (sc := x1) (s := t (S i)) (apC := APc).
           assumption.
           split. replace (S i) with (i + 1). assumption. omega.
           apply H9. assumption. 
Qed.


Lemma mapping_to_reachable_states : 
       forall TSa TSc, Weak_SimRel TSa TSc -> 
                       forall s, reachable s TSc ->
                       forall x, SR (Ap TSa) x s ->  
                       reachable x TSa.
Proof.
   intros.
   unfold reachable.
   assert (W : Weak_SimRel TSa TSc) by apply H.
   induction H.
   induction H0.
   induction H0.
   exists x0. exists x1.
   split. 
   apply trace_inclusion_weak with (TSc := TSc).
   assumption. apply H0.
   apply state_equiv_trans with (sa := x) (sc := s) (s' := (x0 x1)) (apC := (Ap TSc)).
   assumption. assumption. apply H0.

Theorem weak_simulation_relations : 
            forall (prop : LTL_exp)(TSa TSc: TS), 
            Weak_SimRel TSa TSc ->  
            TS_sat_LTLp prop TSa -> 
            TS_sat_LTLp prop TSc.
Proof.
     intros.
     unfold TS_sat_LTLp. intros.
     unfold TS_sat_LTLp in H1.
     destruct TSa as [APa INITa TRa] eqn:A.
     destruct TSc as [APc INITc TRc] eqn:C.
     apply trace_inclusion_weak with (t := trc) in H;
     try (assumption). 
     apply H0; try (assumption).
Qed.
