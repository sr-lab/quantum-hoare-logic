From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.

Definition hoare_triple 
    (np nq: nat)
    (P : Assertion np) 
    (c : com) 
    (Q : Assertion nq) : Prop :=
    forall ns1 ns2 (st1: list (total_map nat * Unitary ns1)) (st2: list (total_map nat * Unitary ns2)), 
    ceval ns1 ns2 c st1 st2 ->
    (Expectation ns1 np st1 P) <= (Expectation ns2 nq st2 Q).

Theorem fy_skip: forall n P, hoare_triple n n P <{skip}> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    unfold Rle.
    right.
    exact (eq_refl).
Qed.

Definition init_sub n (P : Assertion n) : Assertion (n - 1) := 
    pair (fst P) ( ( ⟨0∣ ⊗ (I (2 ^n))) × (snd P) × (∣0⟩ ⊗ (I (2 ^n)))).

Definition apply_sub n (U: Unitary n) (P : Assertion n) : Assertion n :=
    pair (fst P) (Mmult (Mmult U† (snd P)) U).

Definition apply_boolean n (b: bool_exp) (P : Assertion n) : Assertion n :=
    pair (BAnd (fst P) b) (snd P).

Axiom Rlt_trans_eq : forall r1 r2 r3 : R, r1 <= r2 -> r2 <= r3 -> r1 <= r3.

Theorem fy_sequence: forall np nq nr P Q R c1 c2, 
    hoare_triple np nq P c1 Q ->
    hoare_triple nq nr Q c2 R ->
    hoare_triple np nr P <{ c1;c2 }> R.
Proof.
    unfold hoare_triple.
    intros.
    inversion H1.
    subst.
    apply H in H6.
    apply H0 in H9.
    eapply Rlt_trans_eq.
    apply H6.
    apply H9.
Qed.

(*Todo*)
Theorem fy_assign: forall n x e P, 
    hoare_triple n n P <{ x := e }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    - simpl. lra.
    - simpl in H. 
Admitted.

Theorem fy_if: forall (n: nat) (b: bool_exp) (c1 c2: com) P Q, 
    hoare_triple n n (apply_boolean n b P) c1 Q ->
    hoare_triple n n (apply_boolean n <{ ~ b }> P) c2 Q ->
    hoare_triple n n P <{ if b then c1 else c2 end }> Q.
Proof.
    unfold hoare_triple.
    intros.
    inversion H1.
    subst.
Admitted.

Theorem updateStateInitProp: forall n a st, 
   UpdateStateInit n (a :: st) = (if n =? 0
   then (fst a, ∣0⟩⟨0∣) :: UpdateStateInit n st
   else (fst a, ∣ 0 ⟩ ⊗ snd a ⊗ ⟨0∣) :: UpdateStateInit n st).
Proof.
    intros.
    simpl.
    exact (eq_refl).
Qed.

Theorem cvalInit: forall n a st, ceval n (n + 1) <{ new_qubit }> (a :: st)
(UpdateStateInit n (a :: st)) .
Proof.
    intros.
Abort.

Theorem fy_init: forall n P, 
    hoare_triple n n (init_sub n P) <{ new_qubit }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    - simpl. lra. 
    - destruct IHst1.
      + apply E_Init.
      + rewrite -> expectation_sum.
      destruct (ns1 =? n) eqn:nnn.
        * left. eapply Rlt_trans. eapply Rplus_lt_compat_l. apply H0. 
          admit.
        * left. eapply Rlt_trans. eapply Rplus_lt_compat_l. apply H0. 
          admit.
        * simpl. admit.
      + rewrite -> expectation_sum. destruct (ns1 =? n) eqn:nnn.
        * right. rewrite H0. admit.
        * right. rewrite H0. admit.
        * simpl. admit. 
Admitted.

Theorem fy_apply: forall n m G P, 
    hoare_triple n n (apply_sub n (geval G) P) <{ q m *= G }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    - simpl. lra.
    - destruct IHst1.
      + eapply E_AppOne.
      + admit.   
Admitted.

(*TODO*)
Theorem fy_measure: forall n x m P, 
    hoare_triple n n P  <{ x :=meas m }> P.
Proof.
Admitted.

Theorem fy_while: forall n b c P,
    hoare_triple n n (apply_boolean n b P) c P ->
    hoare_triple n n P <{ while b do c end }> (apply_boolean n <{ ~ b }> P).
Proof.
Admitted.

Theorem fy_weakness: forall n c st P Q P' Q',
    hoare_triple n n P c Q ->
    weaker n n n st P' P ->
    weaker n n n st Q Q' ->
    hoare_triple n n P' c Q'.
Proof.
    unfold hoare_triple, weaker.
    intros.
    inversion H1.
    subst.
    apply H in H2.
    eapply Rlt_trans_eq.
Admitted.



 