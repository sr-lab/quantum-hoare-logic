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
    (Expectation ns1 np st1 (P st1)) <= (Expectation ns2 nq st2 (Q st2)).

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

Check UpdateStateAssign. 

Theorem updateAsgnProp: forall n st l x e,
UpdateStateAssign n (st :: l) x e = 
(pair (x !-> (aeval (fst st) e); fst st) (snd st)) :: (UpdateStateAssign n l x e).
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Theorem fy_assign: forall n x e P, 
    hoare_triple n n (fun st => P (UpdateStateAssign n st x e)) <{ x := e }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    - simpl. lra.
    - destruct IHst1.
      + eapply E_Ass.     
Admitted.

Theorem fy_if: forall (n: nat) (b: bool_exp) (c1 c2: com) P Q, 
    hoare_triple n n (fun st => P (Filter n st b)) c1 Q ->
    hoare_triple n n (fun st => P (FilterNeg n st b)) c2 Q ->
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

Theorem fy_init: forall n P, 
    hoare_triple n n (init_sub n P) <{ new_qubit }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    right.
    induction st1.
    - simpl. lra. 
    - destruct IHst1.
      + apply E_Init.
      + destruct (beval (fst a) (fst (init_sub n P (a :: st1)))) eqn:bev1.
        * rewrite expectation_sum.
      destruct (ns1 =? n) eqn:nnn.
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
Admitted.

(*TODO*)
Theorem fy_measure: forall n x m P, 
    hoare_triple n n P  <{ x :=meas m }> P.
Proof.
Admitted.

Theorem fy_while: forall n b c P,
    hoare_triple n n (fun st => P (Filter n st b)) c P ->
    hoare_triple n n P <{ while b do c end }> (fun st => P (FilterNeg n st b)).
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

Definition classicalPropsImp (np nq: nat)(P : Assertion np)
  (Q : Assertion nq) : Prop := forall st sts, beval st (fst (P sts)) = true ->
  beval st (fst (Q sts)) = true .

Theorem fy_imp: forall n c P Q P',
    hoare_triple n n P c Q ->
    classicalPropsImp n n P Q ->
    hoare_triple n n P' c Q.
Proof.
    unfold hoare_triple, classicalPropsImp.
    intros.
Admitted.


 