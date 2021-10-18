From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
Set Printing All.

Definition hoare_triple 
    (np nq: nat)
    (P : Assertion np) 
    (c : com) 
    (Q : Assertion nq): Prop :=
    forall ns1 ns2 
    (st1: list (total_map nat * Unitary (2 ^ ns1))) 
    (st2: list (total_map nat * Unitary (2 ^ ns2))), 
    (ceval ns1 ns2 c st1 st2) ->
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
Axiom Rplus_le_compat_l: forall r r1 r2 : R, r1 <= r2 -> r + r1 <= r + r2.
Axiom Rplus_le_sum_0: forall r r1: R, 0 <= r -> r1 <= r + r1.
Axiom Rplus_lt: forall r1 r2 r3 r4:R, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.

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

Theorem ifHelper: forall n (P: Assertion n) a b,
 beval (mergeMaps (StateOf P) a) b = true ->
 beval (mergeMaps (StateOf P) a) b &&
 beval (mergeMaps (StateOf P) a) (PropOf P) =
 beval (mergeMaps (StateOf P) a) (PropOf P)
.
Proof.
     intros. rewrite H. simpl. reflexivity.
Qed.

Theorem filterTrue : forall n a st b,
beval (fst a) b = true ->
(Filter n (a :: st) b) = a :: (Filter n st b).
Proof.
    intros.
    unfold Filter.
    rewrite H. reflexivity. 
Qed.

Theorem filterFalse : forall n a st b,
beval (fst a) b = false ->
(Filter n (a :: st) b) = (Filter n st b).
Proof.
    intros.
    unfold Filter.
    rewrite H. reflexivity. 
Qed.

Theorem bevalMergeTrue: forall a b n (P: Assertion n),
beval a b = true -> beval (mergeMaps (StateOf P) a) b = true.
Proof.
    (* TODO*)
Admitted.

Theorem bevalMergeFalse: forall a b n (P: Assertion n),
beval a b = false -> beval (mergeMaps (StateOf P) a) b = false.
Proof.
    (* TODO*)
Admitted.

Theorem expect_split: forall n ns2 st' st'' P,
Expectation ns2 n (st' ++ st'') P = 
Rplus (Expectation ns2 n st' P )
(Expectation ns2 n st'' P).
Proof.
    intros.
    induction st'. simpl. lra.
    simpl.
    destruct (beval (mergeMaps (StateOf P) (fst a)) (PropOf P)) eqn:bev.
    rewrite IHst'. rewrite Rplus_assoc. reflexivity.
    rewrite IHst'. reflexivity. 
Qed.

Theorem sum_expects_filters: forall n ns st b P,
Rplus (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b))
(Expectation ns n (Filter ns st <{ ~ b }>) (AssertPreIfTrue P (BNot b)))
= Expectation ns n st P.
Proof.
    intros.
    induction st.
    simpl. lra.
    destruct (beval (fst a) b) eqn:beva.
    simpl. 
    rewrite beva.
    simpl.
    rewrite ifHelper.
    destruct (beval (mergeMaps (StateOf P) (fst a)) (PropOf P)) eqn:beva2.
    destruct (ns =? n) eqn:nsn.
    assert (Heq1: fst (trace (snd a × DensityOf (AssertPreIfTrue P b)))
    = fst (trace (snd a × DensityOf P))).
    unfold DensityOf, AssertPreIfTrue. simpl. reflexivity.
    rewrite Heq1.
    field_simplify.
    assert (Hequiv: (fst (trace (snd a × DensityOf P)) +
    (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b) +
    Expectation ns n (Filter ns st <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)) =
    fst (trace (snd a × DensityOf P)) + Expectation ns n st P)%R).
    rewrite IHst. reflexivity.
    field_simplify in Hequiv.
    apply Hequiv.
    assert (Heq2: fst (trace (snd a ⊗ I (ns - n) × DensityOf (AssertPreIfTrue P b))) 
    = fst (trace (snd a ⊗ I (ns - n) × DensityOf P))).
    unfold DensityOf, AssertPreIfTrue. simpl.
    symmetry.
    unfold DensityOf, AssertPreIfTrue. simpl. reflexivity.
    assert (Hequiv2: (fst (trace (snd a ⊗ I (ns - n) × DensityOf P)) +
    (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b) +
    Expectation ns n (Filter ns st <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)) =
    fst (trace (snd a ⊗ I (ns - n) × DensityOf P)) + Expectation ns n st P)%R).
    rewrite IHst. reflexivity.
    field_simplify in Hequiv2.
    apply Hequiv2.
    apply IHst.
    apply bevalMergeTrue. apply beva.
    simpl.
    rewrite beva. simpl.
    rewrite bevalMergeFalse. simpl.
    destruct (beval (mergeMaps (StateOf P) (fst a)) (PropOf P)) eqn:bev3.
    destruct (ns =? n) eqn:nsn.
    field_simplify.
    assert (Heq: fst (trace (snd a × DensityOf (AssertPreIfTrue P <{ ~ b }>)))
    = fst (trace (snd a × DensityOf P))).
    unfold DensityOf, AssertPreIfTrue. simpl. reflexivity.
    rewrite Heq.
    rewrite (Rplus_comm (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b)) 
    (fst (trace (snd a × DensityOf P)))).
    assert (Hequiv: (fst (trace (snd a × DensityOf P)) +
    (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b) +
    Expectation ns n (Filter ns st <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)) =
    fst (trace (snd a × DensityOf P)) + Expectation ns n st P)%R).
    rewrite IHst. reflexivity.
    field_simplify in Hequiv.
    apply Hequiv.
    assert (Heq: fst (trace (snd a ⊗ I (ns - n) × DensityOf (AssertPreIfTrue P <{ ~ b }>)))
    = fst (trace (snd a ⊗ I (ns - n) × DensityOf P))).
    unfold DensityOf, AssertPreIfTrue. simpl. reflexivity.
    rewrite Heq.
    field_simplify.
    rewrite (Rplus_comm (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b)) 
    (fst (trace (snd a ⊗ I (ns - n) × DensityOf P)))).
    assert (Heq2: fst (trace (snd a ⊗ I (ns - n) × DensityOf (AssertPreIfTrue P b))) 
    = fst (trace (snd a ⊗ I (ns - n) × DensityOf P))).
    unfold DensityOf, AssertPreIfTrue. simpl.
    symmetry.
    unfold DensityOf, AssertPreIfTrue. reflexivity.
    assert (Hequiv2: (fst (trace (snd a ⊗ I (ns - n) × DensityOf P)) +
    (Expectation ns n (Filter ns st b) (AssertPreIfTrue P b) +
    Expectation ns n (Filter ns st <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)) =
    fst (trace (snd a ⊗ I (ns - n) × DensityOf P)) + Expectation ns n st P)%R).
    rewrite IHst. reflexivity.
    field_simplify in Hequiv2.
    apply Hequiv2.
    apply IHst.
    apply beva.
Qed.

Theorem fy_if: forall (n: nat) (b: bool_exp) (c1 c2: com) P Q, 
    hoare_triple n n (AssertPreIfTrue P b) c1 Q ->
    hoare_triple n n (AssertPreIfTrue P (BNot b)) c2 Q ->
    hoare_triple n n P <{ if b then c1 else c2 end }> Q.
Proof.
    unfold hoare_triple.
    intros.
    inversion H1.
    subst.
    apply H in H9. 
    apply H0 in H10.
    assert (Hle: Rplus (Expectation ns1 n (Filter ns1 st1 b) (AssertPreIfTrue P b))
    (Expectation ns1 n (Filter ns1 st1 <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)) 
    = (Expectation ns1 n st1 P)).
    apply sum_expects_filters.
    assert (
        Expectation ns1 n (Filter ns1 st1 b) (AssertPreIfTrue P b)
        + Expectation ns1 n (Filter ns1 st1 <{ ~ b }>) (AssertPreIfTrue P <{ ~ b }>)
        <= (Expectation ns2 n st' Q) + ( Expectation ns2 n st'' Q)
    ).
    apply Rplus_lt. apply H9. apply H10.
    rewrite sum_expects_filters in H2. 
    assert (Hsplit: (Expectation ns2 n st' Q + Expectation ns2 n st'' Q = Expectation ns2 n (st' ++ st'') Q)%R).
    symmetry.
    apply expect_split.
    rewrite <- Hsplit.
    apply H2.
Qed.

Theorem updateStateInitProp: forall n a st, 
   UpdateStateInit n (a :: st) = (if n =? 0
   then (fst a, ∣0⟩⟨0∣) :: UpdateStateInit n st
   else (fst a, ∣ 0 ⟩ ⊗ snd a ⊗ ⟨0∣) :: UpdateStateInit n st).
Proof.
    intros.
    simpl.
    exact (eq_refl).
Qed.

Theorem eqaul_traces_init: forall n (U: Unitary (2 ^ n)) (rho:  Unitary (2 ^ (n - 1))),
trace (rho × (( ⟨0∣ ⊗ (I (2 ^(n - 1)))) × U × (∣0⟩ ⊗ (I (2 ^(n - 1))))))
= trace ( (∣ 0 ⟩ ⊗ rho ⊗ ⟨0∣) × U ).
Proof.
Admitted.

Axiom nateq: forall n m:nat, (n =? m) = true -> n = m.

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
    - rewrite updateStateInitProp.
      destruct (ns1 =? 0) eqn:ns10.
      simpl.
      unfold init_sub. unfold PropOf. simpl. 
      symmetry.
      unfold init_sub. unfold PropOf. simpl.
      unfold DensityOf. simpl.
      symmetry.
      assert (ns1 = 0%nat).
      apply nateq. apply ns10.
      rewrite H0. 
Admitted.

Theorem applyPropCNOT: forall n m a st G,
G = GCNOT ->
(UpdateStateApply n (a :: st) m G) =
(fst a, (padding (n - 2%nat) m (geval G)) 
× (snd a) 
× (padding (n - 2%nat) m (geval G))†) 
:: (UpdateStateApply n st m G).
Proof.
    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem applyPropOracle: forall n m a st G GU,
G = GOracle m GU  ->
(UpdateStateApply n (a :: st) m G) =
(fst a, (padding (n - 3%nat) m (geval G)) 
× (snd a) 
× (padding (n - 3%nat) m (geval G))†) 
:: (UpdateStateApply n st m G).
Proof.   
    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem applyPropOne: forall n m a st G,
G = GH \/ G = GI \/ G = GX \/ G = GY \/ G = GZ ->
(UpdateStateApply n (a :: st) m G) =
(fst a, (padding (n - 1%nat) m (geval G)) 
× (snd a) 
× (padding (n - 1%nat) m (geval G))†) 
:: (UpdateStateApply n st m G).
Proof.
    intros.
    simpl.
    destruct H. 
    rewrite H.
    reflexivity.
    destruct H. 
    rewrite H.
    reflexivity.
    destruct H. 
    rewrite H.
    reflexivity.
    destruct H. 
    rewrite H.
    reflexivity.
    rewrite H.
    reflexivity.
Qed.

Unset Printing Notations.

Theorem equal_traces_apply: forall n m rho 
(M: Unitary (2 ^ m)) 
(U: Unitary (2 ^ n)) ,
fst (trace ( (M × rho × M †) × U)) 
 = fst (trace (rho × ((( M ) †) × U × M))).
Proof.
Admitted.

Theorem fy_apply: forall n m G P, 
    hoare_triple n n (apply_sub n (geval G) P) <{ q m *= G }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    right.
    induction st1.
    - simpl. lra.
    - destruct (beval (mergeMaps (StateOf (apply_sub n (geval G) P)) (fst a))
    (PropOf (apply_sub n (geval G) P))) eqn:bev1. 
    rewrite expectation_sum_true. 
    symmetry.
    destruct G.
    rewrite applyPropOne.
    simpl.
    unfold StateOf, apply_sub, PropOf in bev1. 
    simpl in bev1.
    assert (bev2: beval (mergeMaps (StateOf P) (fst a)) (PropOf P) = true).
    unfold PropOf. apply bev1.
    rewrite bev2.
    assert (Heq: Expectation ns2 n st1 (apply_sub n (geval GH) P) =
    Expectation ns2 n (UpdateStateApply ns2 st1 m GH) P).
    apply IHst1. apply E_AppOne. 
    assert (HH: geval GH = Utils.H). auto.
    rewrite HH in Heq. 
    replace (Expectation ns2 n st1 (apply_sub n Utils.H P) ) 
    with (Expectation ns2 n (UpdateStateApply ns2 st1 m GH) P) by Heq.
    destruct (ns2 =? n) eqn:ns2n.
    assert (Hnns2: n = ns2). apply nateq in ns2n. symmetry. apply ns2n.
    unfold DensityOf, apply_sub. simpl.
    symmetry. unfold DensityOf, apply_sub. simpl.
    Check (padding (ns2 - 1) m Utils.H).
    (* rewrite (equal_traces_apply (padding (ns2 - 1) m Utils.H) (snd a) (snd (snd P)) ns2 n). *)
Admitted.

Definition disjunction {n1 n2 n3}(a1: Assertion n1) 
(a2: Assertion n2) : Assertion n3 := 
   ((_ !-> 0%nat), ((BOr (PropOf a1) (PropOf a2)), ((DensityOf a1) + (DensityOf a2) ))).

Definition AssertPreMeas {n} (P: Assertion n) (x: string) (v: nat) 
  (m : nat) : Assertion n := 
  ( (StateOf P) , ( BAnd (<{ x == v }>) (PropOf P), 
  (GetMeasurementBasis (n - 1%nat) m (v =? 0%nat)) 
  × (DensityOf P) 
  × (GetMeasurementBasis (n - 1%nat) m (v =? 0%nat))†))
.

Theorem fy_measure: forall n x m P, 
    hoare_triple n n (disjunction (AssertPreMeas P x 0%nat m) 
    (AssertPreMeas P x 1%nat m)) <{ x :=meas m }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    simpl. lra.
    simpl.
    destruct (beval (mergeMaps (_ !-> 0%nat) (fst a)) (PropOf P)) eqn:bev1.
Admitted.

Theorem fy_while: forall n b c P,
    hoare_triple n n (AssertPreIfTrue P b) c P ->
    hoare_triple n n P <{ while b do c end }>  (AssertPreIfTrue P (BNot b)).
Proof.
    unfold hoare_triple.
    intros.
    inversion H0.
    subst.
    apply H in H5.
Admitted.

Theorem fy_weakness: forall n c P Q P' Q',
    hoare_triple n n P c Q ->
    (forall ns (st: list (total_map nat * Unitary (2 ^ ns))), weaker ns n n st P' P) ->
    (forall ns (st: list (total_map nat * Unitary (2 ^ ns))), weaker ns n n st Q Q') ->
    hoare_triple n n P' c Q'.
Proof.
    unfold hoare_triple, weaker.
    intros.
    apply H in H2.
    eapply Rlt_trans_eq.
    apply (H0 ns1 st1).
    eapply Rlt_trans_eq.
    apply H2.
    apply (H1 ns2 st2).
Qed.

Definition classicalPropsImp (np nq: nat)(P : Assertion np)
  (Q : Assertion nq) : Prop := forall st, 
  (DensityOf P) = (DensityOf Q) ->
  beval (mergeMaps (StateOf P) st) (PropOf P) = true ->
  beval (mergeMaps (StateOf Q) st) (PropOf Q) = true.

Axiom positive_trace: forall n m (U1: Unitary n) 
(U2: Unitary m), 0 <= fst (trace (Mmult U1 U2)).

Lemma equal_expectations_imp: forall n ns st P Q,
(DensityOf P) = (DensityOf Q) ->
classicalPropsImp n n P Q ->
Expectation ns n st P <= Expectation ns n st Q.
Proof.
    intros.
    induction st.
    simpl. lra.
    simpl.
    unfold classicalPropsImp in H0.
    destruct (beval (mergeMaps (StateOf P) (fst a)) (PropOf P)) eqn:bev.
    rewrite (H0 (fst a)).
    rewrite H.
    destruct (ns =? n) eqn:nsn.
    apply Rplus_le_compat_l.
    apply IHst.
    apply Rplus_le_compat_l.
    apply IHst.
    apply H.
    apply bev.
    assert (Hle: Expectation ns n st Q <=
    (if beval (mergeMaps (StateOf Q) (fst a)) (PropOf Q)
     then
      ((if ns =? n
        then fst (trace (snd a × DensityOf Q))
        else fst (trace (snd a ⊗ I (ns - n) × DensityOf Q))) +
       Expectation ns n st Q)%R
     else Expectation ns n st Q)).
    destruct (beval (mergeMaps (StateOf Q) (fst a)) (PropOf Q)) eqn:bev2.
    destruct (ns =? n) eqn:nsn.
    apply Rplus_le_sum_0.
    apply positive_trace.
    apply Rplus_le_sum_0.
    apply positive_trace.
    right. reflexivity.
    destruct (beval (mergeMaps (StateOf Q) (fst a)) (PropOf Q)) eqn:bev2.
    destruct (ns =? n) eqn:nsn.
    assert(Expectation ns n st Q <=
    fst (trace (snd a × DensityOf Q)) + Expectation ns n st Q).
    apply Rplus_le_sum_0.
    apply positive_trace.
    eapply Rlt_trans_eq.
    apply IHst.
    apply H1.
    assert(Expectation ns n st Q <=
    fst (trace (snd a × DensityOf Q)) + Expectation ns n st Q).
    apply Rplus_le_sum_0.
    apply positive_trace.
    eapply Rlt_trans_eq.
    apply IHst.
    apply Hle.
    apply IHst.
Qed.

Theorem fy_imp_pre: forall n c P Q P',
    hoare_triple n n P c Q ->
    (DensityOf P) = (DensityOf P') ->
    classicalPropsImp n n P' P ->
    hoare_triple n n P' c Q.
Proof.
    unfold hoare_triple.
    intros.
    apply H in H2.
    assert (Hexp: (Expectation ns1 n st1 P') <= (Expectation ns1 n st1 P)).
    apply equal_expectations_imp. symmetry.
    apply H0.
    fold classicalPropsImp in H1.
    apply H1.
    eapply Rlt_trans_eq.
    apply Hexp.
    apply H2.
Qed.

Theorem fy_imp_post: forall n c P Q Q',
    hoare_triple n n P c Q ->
    (DensityOf Q) = (DensityOf Q') ->
    classicalPropsImp n n Q Q' ->
    hoare_triple n n P c Q'.
Proof.
    unfold hoare_triple.
    intros.
    apply H in H2.
    assert (Hexp: (Expectation ns2 n st2 Q) <= (Expectation ns2 n st2 Q')).
    apply equal_expectations_imp. 
    apply H0.
    apply H1.
    eapply Rlt_trans_eq.
    apply H2.
    apply Hexp.
Qed.



 