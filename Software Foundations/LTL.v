(**
   LTL Formalization in Coq by Elaheh Ghassabani
   University of Minnesota
**)

Require Export SfLib.

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
Definition transSys_stateSpace := state -> Prop.
Definition initial_states := state -> Prop. 
Definition transition_relation := state -> state -> Prop.
(**
   We think of Atoms as a set of atomic propositions: if [A : Atoms], 
   [A] includes a set of atomic propositions.
**)
Definition Atoms := atom -> Prop.
 
(** Transition System **)
(*  MWW: comments:
	This is an attempt to characterize the reachable state space.
	There are a few things here that I'm not quite sure about:
		- First, I think that the pre-state of the transition system 
		  should probably be on the left side of the implication.
		  (forall (s s' : state), S s /\ tr s s' ->  S s')
		  
		- The second thing I worry about is this: 
		   (forall (s s' : state), S s' /\ S s -> 
              (forall p, ap p -> s p = s' p) -> s = s')
		  The reason is as follows: 
			Suppose I have two states that agree on values of ap p, but disagree
			on elements of p outside ap.  The equality is not assured!
			The good news is that because we have also constrained the states 
			to be members of S, we can use this to induce equalities across 
			atomic propositions *not in ap* between states in S.
		
		- Without a fixed point, you are *still* going to get strong simulation
			using this definition.  Because you are not restricting S from 
			containing other "stuff".

	(forall (s : state), init s -> S s) /\ 
       (forall (s s' : state), tr s s' /\ S s -> S s') /\

	(* Half-assed definition that might be right; to gain confidence, we would 
       need concrete examples and a proof *)
	(forall (s': state) S s' -> ((init s') \/ (exists s (S s) /\ tr s s'))
	
	p : atom;
	q : atom ; 
	r : atom ; 
	ourS = ???? How do we construct this ???? 
	
*)
Definition TS  (ap : Atoms)(S : transSys_stateSpace)
               (init : initial_states)(tr :transition_relation) :=
       (*(exists s, init s) /\*)
       (forall (s : state), init s -> S s) /\ 
       (forall (s s' : state), S s /\ tr s s' ->  S s') /\
       (*(forall (s s' : state), S s' /\ tr s s' ->  S s) /\*)
       (forall (s': state), S s' -> ((init s') \/ (exists s, S s /\ tr s s'))) /\
       (forall (s s' : state), S s' /\ S s -> 
               (forall p, ap p -> s p = s' p) -> s = s').

(* Theorem Exists_TS ...define TS here... *)
Variable p_ex : atom.
Variable q_ex : atom.
Variable r_ex : atom.
Inductive empty_atom_set : Atoms :=.
Inductive Singleton (x: atom) : Atoms :=
    In_singleton : (Singleton x) x.
Inductive Union (B C: Atoms) : Atoms :=
    | Union_introl : forall x: atom, B x -> (Union B C) x
    | Union_intror : forall x: atom, C x -> (Union B C) x.
Definition Add (B: Atoms) (x: atom) : Atoms := Union B (Singleton x).
Definition ap_ex : Atoms := empty_atom_set.
(*Inductive no_more_mem (ap : Atoms) :=
    | nm : forall (p : atom),  Add ap p = ap /\ (exists x, ap x /\ x = p).*)
Example my_trans_sys : forall (S : transSys_stateSpace)
               (init : initial_states)(tr :transition_relation)
               (s s' : state),
     (TS (Add (Add ap_ex p_ex) q_ex) S init tr /\
     S s /\ S s' /\
     s p_ex = true  /\ s q_ex = false  /\ s r_ex = true /\
     s' p_ex = true /\ s' q_ex = false /\ s' r_ex = false) ->
     s = s'.
Proof.
   intros.
   inversion H. inversion H1. clear H H1. 
   inversion H3. clear H3.
   apply H0. 
   split; assumption. 
   intros.
   assert (p = p_ex \/ p = q_ex).
   Case "Proof_of_assertion".
      inversion H3. subst. inversion H4. inversion H5. inversion H5.
      left. reflexivity. subst.
      inversion H4. right. reflexivity.
   inversion H4. 
   Case "left".
      subst.
      assert (s p_ex = true) by apply H1.
      assert (s' p_ex = true) by apply H1.
      rewrite <- H6 in H5. assumption. subst.
   Case "right".
      subst.
      assert (s q_ex = false) by apply H1.
      assert (s' q_ex = false) by apply H1.
      rewrite <- H6 in H5. assumption.
Qed.
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
Definition subTrace (t : Trace) (n : nat) : Trace := fun i => t (i + n). 
Check subTrace.
(*  
   Trace -> nat -> Trace : [subTrace returns a Trace]
*)



Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* It says:
     (fun i : nat => t (i + m + n)) = (fun i : nat => t (i + (m + n))
*)
Theorem plus_assoc_in_trace : forall (t : Trace) (n m : nat),
       subTrace (subTrace t n) m = subTrace t (m + n).
Proof.
     intros. apply functional_extensionality.
     intros. unfold subTrace. rewrite plus_assoc.
     reflexivity.
Qed.


Theorem subtrace0 : forall (n : nat) (t : Trace),
    subTrace t n = subTrace (subTrace t n) 0.
Proof.
     intros. apply functional_extensionality.
     intros. unfold subTrace. 
     rewrite <- plus_assoc. 
     rewrite plus_O_n. reflexivity.
Qed.

(* a sub-case of subtrace0 *)
Lemma t0 : forall(t : Trace), (subTrace t 0)  = t.
Proof.
     intros. rewrite subtrace0. 
     unfold subTrace.
     apply functional_extensionality.
     intros. 
     repeat (rewrite <- plus_assoc; rewrite <- plus_comm; rewrite plus_O_n). 
     reflexivity.
Qed.



(* 
   If [sf] is a state formula, [sf] belongs to [Atoms].
   State [s] satisfies [sf] if [s sf = true].  
   We can formulate the above fact in Coq. However, for the 
   purpose of this project, we do not need such a formalization explicitly.

Inductive satisfy_sf : atom -> state -> Prop :=
   |state_formula : forall (ap : atom) (s : state), 
                    s ap = true -> satisfy_sf ap s.   
*)

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
     | U   p q => exists n, LTL_sat q (subTrace t n) /\ 
                  (forall (m : nat) (c: m < n), LTL_sat p (subTrace t m))
     | F     p => exists n, LTL_sat p (subTrace t n)
     | G     p => forall (n : nat) , LTL_sat p (subTrace t n)
     | X     p => LTL_sat p (subTrace t 1)
     | W   p q => (exists n, LTL_sat q (subTrace t n) /\ 
                  (forall (m : nat) (c: m < n), LTL_sat p (subTrace t m))) \/ 
                  (forall (m : nat), LTL_sat p (subTrace t m)) 
     end.
(**********************************************************************************************************)

Axiom not_not : forall (p : LTL_exp) (t : Trace),
       ~~ LTL_sat p t <-> LTL_sat p t. 

(***********************************************************************************************************)
(**********************  Theorems **********************)
(*** Basic Tests ***)

(* 
   Trace [t] satisfies atom [ap] iff the first state of the trace,
   i.e. [s0], evaluates [ap] as [true] 
*)
Example test_ap_satisfaction : 
        forall (ap : atom)(t : Trace),
        t 0 ap = true  <-> LTL_sat (AP ap) t.
Proof.
   split;
   intros; simpl;
   simpl in H; assumption.
Qed.


(* 
    Trace [t] does not satisfy atom [ap] iff the first state of
    the trace evaluates [ap] to false 
*)
Example test_ap_satisfaction_2 : 
        forall (ap : atom)(t : Trace),
        t 0 ap = false <-> not (LTL_sat (AP ap) t).
Proof.
   split;
   intros.
   Case "left".
      unfold not. intro. simpl in H0.
      rewrite H0 in H. inversion H.
   Case "right".
      simpl in H.
      apply not_true_is_false in H. assumption.
Qed.


(** 
   Trace [t] does not satisfy LTL property [p] iff [t] satisfies [~p].
   ~ t |= p <->  t |= ~p :
**)
Theorem test_NOT_op : forall (p : LTL_exp) (t : Trace),
        not (LTL_sat p t) <-> LTL_sat (NOT p) t.
Proof.
   split; intros;  simpl; simpl in H; apply H.
Qed.


(**
   Trace [t] satisfies LTL property [AND p q] iff
   [t] satisfies [p] and [t] satisfies [q].
   t |= p /\ q   <->   t |= p  /\ t |= q 
**)
Theorem test_AND_op : forall (p q : LTL_exp) (t : Trace),
       ((LTL_sat p t) /\ (LTL_sat q t)) <-> LTL_sat (AND p q) t.
Proof.
   split; intros; simpl; apply H.
Qed.


(**
   Trace [t] satisfies LTL property [OR p q] iff
   [t] satisfies [p] or [t] satisfies [q].  
   t |= p \/ q  <->    t |= p  \/ t |= q    
**)
Theorem test_OR_op : forall (p q : LTL_exp) (t : Trace),
       ((LTL_sat p t) \/ (LTL_sat q t)) <-> LTL_sat (OR p q) t.
Proof.
   split; intros; simpl; apply H.
Qed.


(**
   Trace [t] satisfies LTL property [IMP p q] iff
   [t] satisfies [q] when [t] satisfies [p].
   t |= p -> q   <->  (t |= p  -> t |= q)
**)
Theorem test_IMP_op : forall (p q : LTL_exp) (t : Trace),
     ((LTL_sat p t) -> (LTL_sat q t)) <-> LTL_sat (IMP p q) t.
Proof.
   split.
   Case " -> ".
      intros. simpl. apply H.
   Case " <- ".
      intro H. simpl in H. apply H.
Qed.

(**************************************************************************************)

(** * Behavioral Equivalence * **)
Definition LTL_equiv (p q : LTL_exp) : Prop :=
     forall (t : Trace),  LTL_sat p t <-> LTL_sat q t.

Theorem LTL_congruence1 : forall (p q r : LTL_exp),
     LTL_equiv p q -> LTL_equiv p r -> LTL_equiv r q.
Proof.
     intros. unfold LTL_equiv.
     unfold LTL_equiv in H.
     unfold LTL_equiv in H0.
     split; intros.
     Case " -> ".
        apply H0 in H1. apply H. assumption. 
     Case " <- ".
        apply H in H1. apply H0. assumption. 
Qed.

Theorem LTL_congruence2 : forall (p q r : LTL_exp),
     LTL_equiv p q -> LTL_equiv q r -> LTL_equiv p r.
Proof.
     intros. unfold LTL_equiv.
     unfold LTL_equiv in H.
     unfold LTL_equiv in H0.
     split; intros.
     Case " -> ".
        apply H0. apply H. assumption. 
     Case " <- ".
        apply H. apply H0. assumption. 
Qed.

Theorem LTL_congruence3 : forall (p q : LTL_exp),
     LTL_equiv p q -> LTL_equiv (NOT p) (NOT q).
Proof.
     intros;
     unfold LTL_equiv in H; unfold LTL_equiv;
     split; intros;
     rewrite <- test_NOT_op; 
     apply test_NOT_op in H0; 
     unfold not; unfold not in H0; intro;  
     apply H in H1; contradiction.
Qed.

Theorem LTL_congruence4 : forall (p q : LTL_exp) (t : Trace),
       LTL_sat p t /\ LTL_equiv p q -> LTL_sat q t.
Proof.
    intros. inversion H.
    unfold LTL_equiv in H1.
    apply H1. assumption.
Qed.
(*********************************************************************************************************)
(**   Equivalance of the drived operators    **)

(*  F p = true U p *)
Theorem F_U : forall (p : LTL_exp),  LTL_equiv (F p)(U TRUE p). 
Proof.
    split.
    Case " -> ".
      intros. inversion H.
      assert (K: forall (m : nat) (c : m < x), LTL_sat TRUE (subTrace t m)).
      SCase "Proof_of_assertion". 
         intros. unfold LTL_sat. apply I.
      simpl. exists x.
      apply conj.
      SCase "left".
         apply H0.
      SCase "right".
         intros. apply I.
    Case " <- ".
      intros. simpl in H.
      simpl. inversion H. inversion H0.
      exists x. apply H1.
Qed.


(* G p = ~F ~ p *)
Theorem G_F : forall (p : LTL_exp), 
           LTL_equiv (G p)(NOT (F (NOT p))).
Proof.
   split.
   Case " -> ".
     intros. simpl in H.
     rewrite <- test_NOT_op.
     unfold not. intros. 
     simpl in H0. inversion H0.
     assert (LTL_sat p (subTrace t x)) by apply H.
     contradiction.
   Case " <- ".
     intros.
     simpl. intros.
     simpl in H. 
     assert (K: ~~ LTL_sat p (subTrace t n)). 
     SCase "Proof_of_assertion".
        unfold not.  intros.
        unfold not in H. apply H.
        exists n. apply H0.
     apply not_not. apply K.
Qed.


(*  p W q = (p U q) \/ G p  *)
Theorem W_U_G : forall (p q: LTL_exp), 
           LTL_equiv (W p q) (OR (U p q)(G p)).
Proof.
   split. rewrite <- test_OR_op.
   Case " -> ".
      intros. simpl in H. inversion H.
      SCase "left".
        left. simpl. apply H0.
      SCase "right".
        right. simpl. apply H0.
   Case " <- ".
      intros. simpl in H. simpl.
      apply H.
Qed.


(* p U q = F q /\ (p W q) *)
Theorem U_F_W : forall (p q: LTL_exp), 
           LTL_equiv (U p q) (AND (F q) (W p q)).
Proof.
   split; rewrite <- test_AND_op.
   Case " -> ".
      intros. simpl in H.
      apply conj; simpl; inversion H; inversion H0.
      SCase "left".
         exists x; apply H1.
      SCase "right".
         left. exists x. apply H0.  
   Case " <- ".
      intros. simpl in H.
      inversion H. inversion H0. inversion H1.
      SCase "left".
         inversion H3. 
         simpl. exists x0. apply H4.
      SCase "right".
         simpl. exists x. apply conj.
         SSCase "left".
             apply H2.
         SSCase "right".
             intros. 
             assert (LTL_sat p (subTrace t m)) by apply H3. 
             apply H4.
Qed.
(******* Some famous laws ********)

(* X is dual with itself :  ~X p = X~ p *)
Theorem X_NOT : forall (p : LTL_exp) ,
                    LTL_equiv (NOT (X p))(X (NOT p)).
Proof.
    split; intros; simpl in H; simpl; apply H.
Qed.



(* F and G are duals of each other  ~G p = F~ p *)
Theorem F_G_duals : forall (p : LTL_exp),
                LTL_equiv (NOT (G p))(F (NOT p)).
Proof.
    split.
    Case " -> ".
        intros. 
        apply test_NOT_op in H.
        assert (LTL_equiv (G p) (NOT (F (NOT p)))) by apply G_F.
        unfold LTL_equiv in H0. 
        rewrite H0 in H.
        rewrite <- test_NOT_op in H.
        apply not_not in H. apply H.
    Case " <- ".
        intros.
        unfold not in H. 
        inversion H. simpl. unfold not; intros.
        apply test_NOT_op in H0. 
        assert (LTL_sat p (subTrace t x)) by apply H1.
        contradiction.
Qed.


(* F and G are duals of each other  ~F p = G~ p *)
Theorem G_F_duals : forall (p : LTL_exp),
             LTL_equiv (NOT (F p))(G (NOT p)).
Proof.
   split. 
   Case " -> ".
     simpl; intros; simpl in H; unfold not; unfold not in H.
     intros. apply H. exists n. apply H0.
   Case " <- ".
     intros.
     assert (forall p', LTL_equiv (G p') (NOT (F (NOT p')))) by apply G_F.
     unfold LTL_equiv in H0. 
     rewrite H0 with (p' := (NOT p)) in H.
     simpl in H.
     simpl.  
     unfold not. intros.
     unfold not in H at 1.  apply H.
     inversion H1. exists x.
     apply not_not. assumption.
Qed.


Lemma subtrace_ex :  forall (p : LTL_exp) (t : Trace),
       (exists n x, LTL_sat p (subTrace (subTrace t x) n)) <->
                 (exists n', LTL_sat p (subTrace t n')).
Proof.
    split.
    Case " -> ".
       intros. inversion H. inversion H0. 
       exists (x + x0).  
       rewrite <- plus_assoc_in_trace with (t := t).  apply H1.
    Case " <- ".
       intros. inversion H. exists x.
       exists 0. rewrite t0. apply H0. 
Qed.
(* Idempotency law : F F p = F p *)
Theorem F_F : forall (p : LTL_exp), 
                  LTL_equiv (F (F p))(F p).
Proof.
   split.
   Case " -> ".
      intros. simpl in H. simpl. inversion H.
      apply subtrace_ex.
      inversion H0.  
      exists x0. exists x. apply H1.
   Case " <- ".
      intros. simpl. simpl in H. 
      exists 0. rewrite t0. apply H.
Qed.


(* Idempotency law: G G p = G p  *)
Theorem G_G : forall (p : LTL_exp), 
           LTL_equiv (G (G p))(G p).
Proof.
    split; intros; simpl in H; simpl.
    Case " -> ".
      intros. 
      assert (LTL_sat p (subTrace (subTrace t 0) n)) by apply H.
      rewrite t0 in H0.
      apply H0.
    Case " <- ".
      intros.
      assert (LTL_sat p (subTrace t (n0 + n))) by apply H.
      rewrite plus_assoc_in_trace. apply H0.
Qed.


(************************************************************************************************)
(************************************************************************************************)
           
(***********  Simulation Relations ************)
                           

Definition state_equiv (sa sc : state) (apA : Atoms) : Prop :=
             forall p, apA p -> sa p = sc p.

(* Trace of a transition system *)
Definition trace_of_ts (t : Trace) (ap : Atoms)(S : transSys_stateSpace)
                       (init : initial_states)(tr : transition_relation) := 
            TS ap S init tr -> 
           (exists s, init s /\ state_equiv s (t 0) ap) /\
           (forall (i : nat), exists s s', tr s s' /\ S s /\ S s' /\
                    state_equiv s (t i) ap /\ state_equiv s' (t (i+1)) ap).    

Check trace_of_ts.


(* 
   Definition of Simulation Relations
*)

Definition SR (sa sc : state)(apA : Atoms) :=  state_equiv sa sc apA.


(**
  Conditions under which two machines (A and C) simulate each other:
**)
Definition SimRelCond (apA apC : Atoms)(Sa Sc : transSys_stateSpace)
                      (ia ic : initial_states)
                      (ta tc : transition_relation):=
      TS apA Sa ia ta /\ TS apC Sc ic tc ->
      (forall (p : atom), apA p -> apC p) /\
      (forall (s : state), ic s -> exists s', ia s' /\ state_equiv s' s apA).

(* Transition system A simulates transtion system C: *)
Inductive A_simulates_C (apA apC : Atoms)(Sa Sc : transSys_stateSpace)
                        (ia ic : initial_states)(ta tc : transition_relation):=
   sim : 
        SimRelCond apA apC Sa Sc ia ic ta tc ->  
        (forall (sa sc sc' : state), Sa sa /\ Sc sc /\ Sc sc' ->
                (SR sa sc apA) /\ tc sc sc' -> 
        (exists sa', Sa sa' /\ ta sa sa' /\  SR sa' sc' apA)) ->
        A_simulates_C apA apC Sa Sc ia ic ta tc.




Lemma state_equiv_trans : forall (sa sc s' : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv sa sc apA -> state_equiv sc s' apC ->
       state_equiv sa s' apA.
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
       state_equiv sa sc apC -> state_equiv sa sc apA.
Proof.
   intros.
   unfold state_equiv in H0.
   unfold state_equiv.
   intros.
   apply H in H1. apply H0 in H1. assumption.
Qed.


Lemma state_equiv_comm : forall (s s' : state) (ap : Atoms),
      state_equiv s s' ap <-> state_equiv s' s ap.
Proof.
    intros. split; unfold state_equiv; intros;
    apply H in H0; rewrite H0; reflexivity.
Qed. 
Lemma state_equiv_imp : forall (sa sc s : state) (apA apC : Atoms),
       (forall (p : atom), apA p -> apC p) -> 
       state_equiv sa s apA /\ state_equiv sc s apC ->
       state_equiv sa sc apA.
Proof.
    intros. unfold state_equiv. intros.
    unfold state_equiv in H0. inversion H0. clear H0.
    assert (apA p) by assumption.
    apply H2 in H1. 
    apply H in H0. apply H3 in H0. rewrite <- H1 in H0.
    symmetry. assumption.
Qed.
(*
  If [A] simulate5 [C], every trace of [C] has an equivalent
  trace in [A].
*)
Lemma trace_inclusion : forall (apA apC: Atoms) (Sa Sc : transSys_stateSpace)
                        (ia ic : initial_states)
                        (ta tc : transition_relation),
           TS apA Sa ia ta /\ TS apC Sc ic tc ->
           A_simulates_C apA apC Sa Sc ia ic ta tc ->
          (forall (t : Trace), trace_of_ts t apC Sc ic tc ->
           trace_of_ts t apA Sa ia ta).
Proof.
     intros;
     unfold trace_of_ts; intros.
     unfold trace_of_ts in H1. 
     inversion H. apply H1 in H4. clear H1 H2.
     inversion H4; inversion H1; clear H4 H1;
     inversion H0.
     clear H0.
     inversion H;
     unfold SimRelCond in H1. apply H1 in H; clear H1. 
     inversion H. clear H.
     assert (ic x -> exists s, ia s /\ state_equiv s x apA) by apply H7;
     clear H7.
     inversion H5. apply H in H7; clear H.
     inversion H7. inversion H; clear H7 H.
     split. 
     Case "left" .
       exists x0. split.
       SCase "left".
         assumption.
       SCase "right".
         apply state_equiv_trans with (sc := x) (apC := apC).
         assumption. assumption. assumption.
    Case "right".
      intros.
      induction i.
      SCase "i is O".
        exists x0.
        assert (exists s s', tc s s' /\ Sc s /\ Sc s' /\  state_equiv s (t 0) apC /\
                               state_equiv s' (t 1) apC) by apply H2.
        inversion H. inversion H7; clear H H7.
        inversion H11. inversion H7; clear H11 H7.
        assert (Sa x0 /\ Sc x1 /\ Sc x2 ->
                SR x0 x1 apA /\ tc x1 x2 ->
                exists s, Sa s /\ ta x0 s /\ SR s x2 apA) by apply H4; clear H4.
        assert (TC: tc x1 x2) by assumption.
        inversion H5. apply H6 in H4.
        assert (x = x1).
        SSCase "Proof_of_assertion".
           assert (Sc x /\ Sc x1). split. assumption. assumption.
           assert (Sc x /\ Sc x1 -> state_equiv x (t 0) apC /\ 
                                    state_equiv x1 (t 0) apC).
           SSSCase "Proof_of_assertion".
                intros. split. assumption. apply H13.
                apply H6. split; apply H14.
                intros. 
                assert (x1 p = (t 0) p). apply H15; assumption.
                assert (x p = (t 0) p). apply H11; assumption.
                rewrite <- H17 in H18; assumption.
        subst. clear H12.
        assert (Sa x0 /\ Sc x1 /\ Sc x2).
        SSCase "Proof_of_assertion".
          split. apply H0 in H9. assumption. split. assumption. apply H13.
        apply H7 in H12; clear H7. inversion H12. clear H4. 
        inversion H7. inversion H14; clear H14 H7.
        exists x. split. 
        SSCase "left". 
          assumption.
        SSCase "right".
          split.
          SSSCase "left".
             apply state_equiv_trans with (sa := x0) (apA := apA)
                     (sc := x1) (s' := (t 0)) (apC := apC)  in H11;
             try (apply H3 in H9); assumption.
          SSSCase "right".
             rewrite plus_O_n. 
             split. assumption. split.
             apply state_equiv_imp with (sa := x0) (apA := apA)
                     (s := x1) (sc := (t 0)) (apC := apC).
             assumption. split. assumption. apply state_equiv_comm. assumption.
             apply state_equiv_trans with (sa := x) (apA := apA)
                     (sc := x2) (s' := (t 1)) (apC := apC). assumption.
             apply H16. apply H13.
        split. 
        SSCase "left".
          apply H10. 
        SSCase "right".
          assumption.


    SCase "i is S i'".
       inversion IHi;  inversion H; clear IHi H.
       inversion H7. inversion H11; clear H11.
       exists x2. 
       assert (exists s s', tc s s' /\ Sc s /\ Sc s' /\ state_equiv s (t (S i)) apC /\
               state_equiv s' (t (S i + 1)) apC) by apply H2; clear H2.
       inversion H11. inversion H2; clear H11 H2.
       inversion H14; clear H14.
       assert (Sa x2 /\ Sc x3 /\ Sc x4 ->
               SR x2 x3 apA /\ tc x3 x4 ->
               exists s, Sa s /\ ta x2 s /\ SR s x4 apA) by apply H4; clear H4.
       assert (TCx : tc x3 x4) by assumption.
       assert (Sa x2 /\ Sc x3 /\ Sc x4).
       SSCase "Proof_of_assertion".
          split. apply H7. split; apply H11.
       apply H14 in H4; clear H14. inversion H4; inversion H14; clear H4 H14.
       exists x5. split.
       SSCase "left".
          apply H16.
       SSCase "right". 
          split.
          SSSCase "left".
             replace (S i) with (i + 1); try (apply H7);
             rewrite plus_comm. reflexivity.
          SSCase "right".
             inversion H16.
             split. assumption. split. 
             replace (S i) with (i + 1).
             apply H13. rewrite plus_comm. reflexivity.
             apply state_equiv_trans with (sa := x5) (apA := apA)
                     (sc := x4) (s' := (t (S i + 1))) (apC := apC);
             try (assumption). apply H11.  split.
             inversion H11.
             apply state_equiv_imp with (sa := x2) (sc := x3)
                      (s := (t (i + 1))) (apA := apA) (apC := apC); 
             try (assumption). split. apply H13.
             rewrite plus_comm. apply H11.
             assumption.
Qed.



(** 
    The meaning of the notion that transition system [ts] satisfies 
    LTL property [p]: 
 **)
Definition TS_sat_LTLp (prop : LTL_exp)(ap : Atoms)
                       (S : transSys_stateSpace)
                       (init : initial_states)
                       (tr :transition_relation) :=
       TS ap S init tr ->
       (forall (trc : Trace), 
       trace_of_ts trc ap S init tr ->  LTL_sat prop trc).

(*
  if [A] simulates [C], 
  every LTL properties satisfied by [A] is also satisfied by [C].
*)     
Theorem simulation_relations : 
            forall (prop : LTL_exp)(apA apC: Atoms) 
                   (Sa Sc : transSys_stateSpace)
                   (ia ic : initial_states)
                   (ta tc : transition_relation),
            TS apA Sa ia ta /\ TS apC Sc ic tc ->
            A_simulates_C apA apC Sa Sc ia ic ta tc ->  
            TS_sat_LTLp prop apA Sa ia ta -> 
            TS_sat_LTLp prop apC Sc ic tc.
Proof.
     intros.
     unfold TS_sat_LTLp. intros.
     unfold TS_sat_LTLp in H1.
     apply trace_inclusion with (t := trc) in H0;
     try (assumption). 
     apply H1; try (assumption). apply H.
Qed.
