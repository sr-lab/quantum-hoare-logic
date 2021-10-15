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
    (Q : Assertion nq): Prop :=
    forall ns1 ns2 
    (st1: list (total_map nat * Unitary (2 ^ ns1))) 
    (st2: list (total_map nat * Unitary (2 ^ ns2))), 
    ceval ns1 ns2 c st1 st2 ->
    (Expectation ns1 np st1 P) 
     <= (Expectation ns2 nq st2 Q).

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

Axiom Rlt_trans_eq : forall r1 r2 r3 : R, 
r1 <= r2 -> r2 <= r3 -> r1 <= r3.

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

Definition AssertPreAsgn {n} (P: Assertion n) (x: string) 
 (e: nat) : Assertion n := (pair (x !-> e; _ !-> 0%nat)
 (pair (PropOf P) (DensityOf P))).

Theorem eq_maps: forall x e a,
 (mergeMaps (_ !-> 0%nat) (x !-> e; a)) 
 = (mergeMaps (x !-> e; _ !-> 0%nat) a).
Proof.
(* TODO *)
Admitted.

Theorem equal_evals_asgn: forall n a (P: Assertion n) x e, 
StateOf P = t_empty 0%nat ->
beval (mergeMaps (StateOf (AssertPreAsgn P x e)) a) (PropOf (AssertPreAsgn P x e)) = true ->
beval (mergeMaps (StateOf P) (x !-> aeval a e; a)) (PropOf P) = true.
Proof.
    intros.
    simpl.
    simpl in H0.
    assert (prp: (PropOf (AssertPreAsgn P x e) = PropOf P)).
    unfold AssertPreAsgn, PropOf. simpl. reflexivity.
    rewrite prp in H0.
    rewrite H. 
    rewrite eq_maps.
    apply H0.
Qed.

Theorem fy_assign: forall n x e P, 
    StateOf P =  t_empty 0%nat ->
    hoare_triple n n (AssertPreAsgn P x e) <{ x := e }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H0.
    subst.
    right.
    induction st1.
    - simpl. lra.
    - destruct (beval (mergeMaps (StateOf (AssertPreAsgn P x e)) (fst a))
    (PropOf (AssertPreAsgn P x e))) eqn:beval1.
      + rewrite expectation_sum_true.
        symmetry.
        rewrite updateAsgnProp.
        assert (APAEA: DensityOf (AssertPreAsgn P x e) = DensityOf P). 
        unfold AssertPreAsgn, DensityOf. simpl. reflexivity.
        rewrite APAEA. 
        assert (HlPR : Expectation ns2 n st1 (AssertPreAsgn P x e) =
        Expectation ns2 n (UpdateStateAssign ns2 st1 x e) P). apply IHst1.
        apply E_Ass. rewrite HlPR. simpl. simpl in beval1. 
        assert (beval2: beval (mergeMaps (StateOf P) (x !-> e; fst a)) (PropOf P) = true).
        assert (PAPAP: PropOf (AssertPreAsgn P x e) = PropOf P).
        unfold PropOf, AssertPreAsgn. simpl. reflexivity.
        rewrite PAPAP in beval1. rewrite H. rewrite eq_maps. apply beval1.
        rewrite beval2. reflexivity.
        apply beval1.
    + rewrite expectation_sum_false. symmetry. rewrite updateAsgnProp.
      simpl.
      assert (beval2: beval (mergeMaps (StateOf P) (x !-> e; fst a)) (PropOf P) = false).
      assert (PAPAP: PropOf (AssertPreAsgn P x e) = PropOf P).
      unfold PropOf, AssertPreAsgn. simpl. reflexivity. rewrite PAPAP in beval1. rewrite H. 
      rewrite eq_maps. apply beval1. rewrite beval2. 
      assert (HlPR : Expectation ns2 n st1 (AssertPreAsgn P x e) =
        Expectation ns2 n (UpdateStateAssign ns2 st1 x e) P). 
        apply IHst1. apply E_Ass. rewrite HlPR. reflexivity. 
      apply beval1.
Qed.

Definition AssertPreIfTrue {n} (P: Assertion n) (b: bool_exp)
 : Assertion n := (pair (StateOf P)
 (pair (BAnd b (PropOf P)) (DensityOf P))).

Theorem fy_if: forall (n: nat) (b: bool_exp) (c1 c2: com) P Q, 
    hoare_triple n n (AssertPreIfTrue P b) c1 Q ->
    hoare_triple n n (AssertPreIfTrue P (BNot b)) c2 Q ->
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
    - destruct (beval (mergeMaps (StateOf (init_sub n P))
     (fst a)) (PropOf (init_sub n P))) eqn:beval1. 
     assert (Heq: Expectation ns1 n st1 (init_sub n P) =
     Expectation (ns1 + 1) n (UpdateStateInit ns1 st1) P). 
     apply IHst1. apply E_Init. rewrite expectation_sum_true.
     unfold init_sub. symmetry. rewrite updateStateInitProp.
     (* rewrite expectation_sum_true. *) admit. 
     apply beval1. rewrite expectation_sum_false.
     assert (Heq2: Expectation ns1 n st1 (init_sub n P) =
     Expectation (ns1 + 1) n (UpdateStateInit ns1 st1) P).  apply IHst1. 
     apply E_Init. rewrite Heq2. symmetry.
      (* rewrite expectation_sum_false. *) admit.
     apply beval1.
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
    hoare_triple n n (AssertPreIfTrue P b) c P ->
    hoare_triple n n P <{ while b do c end }>  (AssertPreIfTrue P (BNot b)).
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
  (Q : Assertion nq) : Prop := forall st, 
  beval (mergeMaps (StateOf P) st) (PropOf P) = true ->
  beval (mergeMaps (StateOf P) st) (PropOf Q) = true .

Theorem fy_imp: forall n c P Q P',
    hoare_triple n n P c Q ->
    classicalPropsImp n n P Q ->
    hoare_triple n n P' c Q.
Proof.
    unfold hoare_triple, classicalPropsImp.
    intros.
Admitted.


 