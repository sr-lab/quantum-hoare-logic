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
Axiom nminusplus: forall n, (n - 1 + 1)%nat = n.
Axiom pow2_simp: forall n m: nat, ((2 ^ m) * (2 ^ ((m - n))))%nat = (2 ^ n)%nat.
Lemma Rplus_cancel_l : forall r1 r2 r3, (r1 + r2)%R = (r1 + r3)%R -> r2 = r3.
Proof.
  intros.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

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
mergeMaps (x !-> e; a) (_ !-> 0%nat)
 = mergeMaps (a) (x !-> e; _ !-> 0%nat).
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
    simpl. lra.
    rewrite updateAsgnProp.
    simpl.
    assert (PAPAP: PropOf (AssertPreAsgn P x e) = PropOf P).
    unfold PropOf, AssertPreAsgn. simpl. reflexivity.
    assert (APAEA: DensityOf (AssertPreAsgn P x e) = DensityOf P). 
    unfold AssertPreAsgn, DensityOf. simpl. reflexivity.
    rewrite PAPAP.
    rewrite APAEA.
    rewrite H.
    rewrite eq_maps.
    destruct (beval (mergeMaps (fst a) (x !-> e; _ !-> 0%nat)) (PropOf P)) eqn:bev1.
    rewrite IHst1.
    reflexivity.
    apply E_Ass.
    rewrite IHst1.
    reflexivity.
    apply E_Ass.
Qed.

Definition AssertPreIfTrue {n} (P: Assertion n) (b: bool_exp)
 : Assertion n := (pair (StateOf P)
 (pair (BAnd b (PropOf P)) (DensityOf P))).

Theorem ifHelper: forall n (P: Assertion n) a b,
 beval (mergeMaps a (StateOf P)) b = true ->
 beval (mergeMaps a (StateOf P)) b &&
 beval (mergeMaps a (StateOf P)) (PropOf P) =
 beval (mergeMaps a (StateOf P)) (PropOf P).
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
beval a b = true -> beval (mergeMaps a (StateOf P)) b = true.
Proof.
    (* TODO*)
Admitted.

Theorem bevalMergeFalse: forall a b n (P: Assertion n),
beval a b = false -> beval (mergeMaps a (StateOf P)) b = false.
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
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:bev.
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
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:beva2.
    assert (Heq1: 
    (fst (trace ( (complement ns n (snd a))
       × (complement n ns (DensityOf (AssertPreIfTrue P b))))))
    = (fst (trace ((complement ns n (snd a)) × (complement n ns (DensityOf P)))))).
    unfold AssertPreIfTrue, DensityOf. simpl. reflexivity.
    rewrite Heq1.
    rewrite Rplus_assoc.
    rewrite IHst.
    reflexivity.
    rewrite IHst.
    reflexivity.
    apply bevalMergeTrue. 
    apply beva.
    simpl.
    rewrite beva. simpl.
    rewrite bevalMergeFalse. simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:bev2.
    assert (Heq1: 
    (fst (trace
      (complement ns n (snd a)
       × complement n ns (DensityOf (AssertPreIfTrue P <{ ~ b }>)))))
    = (fst (trace ((complement ns n (snd a)) × (complement n ns (DensityOf P)))))).
    unfold AssertPreIfTrue, DensityOf. simpl. reflexivity.
    rewrite Rplus_comm.
    rewrite Heq1.
    rewrite Rplus_assoc.
    rewrite Rplus_comm in IHst.
    rewrite IHst.
    reflexivity.
    rewrite IHst.
    reflexivity.
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
   UpdateStateInit n (a :: st) = 
   (if n =? 0 
      then (fst a, ∣0⟩⟨0∣) 
      else (fst a, ∣ 0 ⟩ ⊗ snd a ⊗ ⟨0∣)) 
   :: (UpdateStateInit n st).
Proof.
    intros.
    simpl.
    destruct (n =? 0) eqn:n0.
    reflexivity. reflexivity.
Qed.

Axiom nateq: forall n m:nat, (n =? m) = true -> n = m.

Lemma init_sub_beval_equal: forall (n ns: nat) (P: Assertion n) (a: total_map nat * Unitary (2 ^ ns)),
beval (mergeMaps (fst a) (StateOf P)) (PropOf (init_sub n P)) 
= beval (mergeMaps (fst a) (StateOf P)) (PropOf P).
Proof.
    intros.
    unfold init_sub, PropOf.
    simpl.
    reflexivity. 
Qed.

Lemma equal_traces_init_ns_0: forall (n: nat) a
(P: Assertion n),
fst (trace (complement 1 n ∣0⟩⟨0∣ × complement n 1 (DensityOf P))) 
= fst (trace
   (complement 0 (n + 1) a
    × complement (n + 1) 0 (DensityOf (init_sub n P)))).
Proof.
Admitted.

Lemma equal_traces_init_ns_gt_0: forall (n ns: nat) (a: Unitary (2^ns))
(P: Assertion n),
fst
   (trace
      (complement ns (n + 1) a
       × complement (n + 1) ns (pre_init n (snd (snd P)))))
= 
fst
(trace
   (complement (ns + 1) n (∣ 0 ⟩ ⊗ a ⊗ ⟨0∣)
    × complement n (ns + 1) (snd (snd P)))).
Proof.
Admitted.

Theorem fy_init: forall n P, 
    hoare_triple (n + 1%nat) n (init_sub n P) <{ new_qubit }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    right.
    induction st1.
    simpl. lra.
    rewrite updateStateInitProp.
    destruct (ns1 =? 0) eqn:ns10.
    simpl.
    rewrite init_sub_beval_equal.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:bev.
    rewrite IHst1.
    field_simplify. symmetry. field_simplify.
    remember (Expectation (ns1 + 1) n (UpdateStateInit ns1 st1) P) as r.
    assert (Hns1: ns1 = 0%nat).
    apply nateq. apply ns10.
    rewrite Hns1. simpl.
    rewrite (equal_traces_init_ns_0 n (snd a) P).
    reflexivity.
    apply E_Init.
    rewrite IHst1.
    reflexivity.
    apply E_Init.
    simpl.
    rewrite init_sub_beval_equal.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:bev.
    rewrite IHst1.
    unfold init_sub, DensityOf. simpl.
    remember (Expectation (ns1 + 1) n (UpdateStateInit ns1 st1) P) as r.
    rewrite equal_traces_init_ns_gt_0.
    reflexivity.
    apply E_Init.
    rewrite IHst1.
    reflexivity.
    apply E_Init.
Qed.

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
    repeat (try destruct H;  
    try rewrite H;
    try reflexivity).
Qed.

Theorem applyPropTwo: forall n m a st G,
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

Theorem equal_traces_apply: forall (n ns m: nat) (G: Unitary 2)
(P: Assertion n) (a: Unitary (2^ns)),
fst
   (trace
      ((complement ns n a)
       × (complement n ns (DensityOf (apply_sub n G P)))))
=
fst
   (trace
      ((complement ns n ((padding (ns - 1) m G) × a
          × (padding (ns - 1) m G) †))
       × (complement n ns (DensityOf P)))).
Proof.
Admitted.

Theorem equal_traces_apply_cnot: forall (n ns m: nat) (G: Unitary 2)
(P: Assertion n) (a: Unitary (2^ns)),
fst
   (trace
      ((complement ns n a)
       × (complement n ns (DensityOf (apply_sub n G P)))))
=
fst
   (trace
      ((complement ns n ((padding (ns - 2) m G) × a
          × (padding (ns - 2) m G) †))
       × (complement n ns (DensityOf P)))).
Proof.
Admitted.

Theorem equal_traces_apply_oracle: forall (n ns m: nat) (G: Unitary 2)
(P: Assertion n) (a: Unitary (2^ns)),
fst
   (trace
      ((complement ns n a)
       × (complement n ns (DensityOf (apply_sub n G P)))))
=
fst
   (trace
      ((complement ns n ((padding (ns - 3) m G) × a
          × (padding (ns - 3) m G) †))
       × (complement n ns (DensityOf P)))).
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
    simpl. lra.
    destruct G.
    rewrite applyPropOne.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n Utils.H P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply n ns2 m Utils.H P (snd a)).
    replace (Utils.H) with (geval GH).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace (Utils.H) with (geval GH).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    left. auto.
    rewrite applyPropOne.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n Utils.X P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply n ns2 m Utils.X P (snd a)).
    replace (Utils.X) with (geval GX).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace (Utils.X) with (geval GX).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    right. right. auto.
    rewrite applyPropOne.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n Utils.Y P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply n ns2 m Utils.Y P (snd a)).
    replace (Utils.Y) with (geval GY).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace (Utils.Y) with (geval GY).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    right. right. right. auto.
    rewrite applyPropOne.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n Utils.Z P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply n ns2 m Utils.Z P (snd a)).
    replace (Utils.Z) with (geval GZ).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace (Utils.Z) with (geval GZ).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    right. right. right. right. auto.
    rewrite applyPropOne.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n (I 2) P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply n ns2 m (I 2) P (snd a)).
    replace (I 2) with (geval GI).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace (I 2) with (geval GI).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    right. auto.
    rewrite applyPropTwo.
    simpl.
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf (apply_sub n CNOT P))) eqn:bev1.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    rewrite (equal_traces_apply_cnot n ns2 m (CNOT) P (snd a)).
    replace (CNOT) with (geval GCNOT).
    rewrite IHst1.
    reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    assert (bev2: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = false).
    unfold apply_sub, PropOf in bev1. simpl in bev1. apply bev1.
    rewrite bev2.
    replace CNOT with (geval GCNOT).
    rewrite IHst1. reflexivity.
    apply E_AppOne.
    simpl. reflexivity.
    auto.
Qed.

Theorem mergeSameMaps: forall mp, (mergeMaps mp mp) = mp.
Proof.
Admitted.

Definition disjunction {n} (a1 a2: Assertion n) : Assertion n := 
   ((_ !-> 0%nat), ((BOr (PropOf a1) (PropOf a2)), ((DensityOf a1) + (DensityOf a2) ))).

Axiom reduce_merge_maps: forall mp, mergeMaps mp (_ !-> 0%nat) = mp.

Lemma distrib_disjunction: forall n ns a P Q,
(fst
   (trace
      ((complement ns n a)
       × (complement n ns (DensityOf (disjunction P Q))))))
= ((fst (trace ((complement ns n a) × (complement n ns (DensityOf P))))) +
(fst (trace ((complement ns n a) × (complement n ns (DensityOf Q))))))%R.
Proof.
Admitted.

Lemma disjunction_expectation: forall n ns st P Q,
(Expectation ns n st (disjunction P Q)) = 
((Expectation ns n st P) +
(Expectation ns n st Q))%R.
Proof.
    intros.
    induction st.
    simpl.
    lra.
    simpl.
    rewrite reduce_merge_maps.
    destruct (beval (fst a) (PropOf P)) eqn:bev1.
    destruct (beval (fst a) (PropOf Q)) eqn:bev2.
    simpl.
    assert (bev3: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    apply bevalMergeTrue. apply bev1.
    assert (bev4: beval (mergeMaps (fst a) (StateOf Q)) (PropOf Q) = true).
    apply bevalMergeTrue. apply bev2.
    rewrite bev3.
    rewrite bev4.
    rewrite distrib_disjunction.
    remember (fst (trace (complement ns n (snd a) × complement n ns (DensityOf P)))) as r1.
    remember (fst (trace (complement ns n (snd a) × complement n ns (DensityOf Q)))) as r2.
    field_simplify.
    rewrite IHst.
    field_simplify.
    reflexivity.
    simpl.
    assert (bev3: beval (mergeMaps (fst a) (StateOf P)) (PropOf P) = true).
    apply bevalMergeTrue. apply bev1.
    assert (bev4: beval (mergeMaps (fst a) (StateOf Q)) (PropOf Q) = false).
    apply bevalMergeFalse. apply bev2.
    rewrite bev3.
    rewrite bev4.
Admitted.

Definition AssertPreMeas {n} (P: Assertion n) (x: string) (v: nat) 
  (m : nat) : Assertion n := 
  ( (x !-> v; StateOf P) , ( (PropOf P), 
  (GetMeasurementBasis (n - 1%nat) m (v =? 0%nat)) 
  × (DensityOf P) 
  × (GetMeasurementBasis (n - 1%nat) m (v =? 0%nat))†)).

Theorem morgan_or_and: forall a P, orb (andb a P) (andb (negb a) P) = P.
Proof.
    intros.
    destruct a eqn:ca.
    simpl. 
    repeat(destruct P eqn:pa; auto).
    simpl. reflexivity.
Qed.

Theorem expectation_post_meas_split: forall n ns a st x m P,
(Expectation ns n (UpdateStateMeasure ns (a :: st) x m) P)
<= 
  (( if beval (fst a) (PropOf P) then 
        if ns =? n then 
            (fst (trace (((GetMeasurementBasis (n - 1%nat) m true) 
              × (snd a) 
              × (GetMeasurementBasis (n - 1%nat) m true)† )
              × (DensityOf P) )))
        else 
            (fst (trace (((GetMeasurementBasis (n - 1%nat) m true) 
              × (snd a ⊗ I (2 ^ (ns - n))) 
              × (GetMeasurementBasis (n - 1%nat) m true)† )
              × (DensityOf P) )))
     else 0%R  
   ) +
   ( if beval (fst a) (PropOf P) then 
        if ns =? n then 
            (fst (trace ((GetMeasurementBasis (n - 1%nat) m false) 
              × (snd a) 
              × (GetMeasurementBasis (n - 1%nat) m false)† 
              × (complement n ns (DensityOf P)) )))
        else 
            (fst (trace ((GetMeasurementBasis (n - 1%nat) m false) 
              × (snd a ⊗ I (2 ^ (ns - n))) 
              × (GetMeasurementBasis (n - 1%nat) m false)† 
              × (complement n ns (DensityOf P)) ))) 
     else 0%R
   ) + 
(Expectation ns n (UpdateStateMeasure ns st x m) P))%R.
Proof.
    intros.
    destruct (beval (fst a) (PropOf P)) eqn:beva.
    destruct (ns =? n) eqn:nsn.
    simpl.
    destruct (beval (mergeMaps (StateOf P) (x !-> 0%nat; fst a)) (PropOf P)) eqn:bev1.
    destruct (beval (mergeMaps (StateOf P) (x !-> 1%nat; fst a)) (PropOf P)) eqn:bev2.
Admitted.

Lemma traces_sum: forall {n} (m1 m2: Matrix n n),
  fst (trace (m1 + m2)) = ((fst (trace m1)) + (fst (trace m2)))%R.
Proof.
Admitted.

Lemma matrices_distributive: forall {n} (m1 m2 m3: Matrix n n),
m1 × (m2 + m3) = m1 × m2 + m1 × m3.
Proof.
Admitted.

Lemma equal_traces_mult: forall {n} (p1 p2 p3: Matrix n n),
fst (trace (p1 × (p2 × p3 × (p2) †))) = fst (trace (p2 × p1 × (p2) † × p3)).
Proof.
Admitted.

Lemma equivalent_with_respect_to_x: forall n st (P: Assertion n) x v,
beval (mergeMaps st (x !-> v; StateOf P)) (PropOf P)
= beval (mergeMaps (x !-> v; st) (StateOf P)) (PropOf P).
Proof.
Admitted.

Definition conjunction {n: nat} (P1: Assertion n) 
(P2: Assertion n) : (Assertion n) := 
((_ !-> 0%nat), (BAnd (PropOf P1) (PropOf P2), (DensityOf P1) + (DensityOf P2))).

Lemma conjunction_expectation: forall n ns a st (P1 P2: Assertion n),
Expectation ns n (a :: st) (conjunction P1 P2)
 = (if
 beval (mergeMaps (fst a) (StateOf P1)) (PropOf P1) &&
 beval (mergeMaps (fst a) (StateOf P2)) (PropOf P2)
then
 ((fst (trace ( (complement ns n (snd a))
        × (complement n ns (DensityOf (conjunction P1 P2)))))) +
  (Expectation ns n st (conjunction P1 P2)))%R
else
 (Expectation ns n st (conjunction P1 P2))).
Proof.
Admitted.

Theorem equal_traces_meas: forall n ns m x a P,
fst
  (trace
     (complement ns n a
      × complement n ns
          (DensityOf
             (conjunction (AssertPreMeas P x 0 m) (AssertPreMeas P x 1 m)))))
=
((fst (trace 
        (complement ns n
            (GetMeasurementBasis (ns - 1) m true × a
                 × (GetMeasurementBasis (ns - 1) m true) †)
            × complement n ns (DensityOf P)))) +
(fst
    (trace
        (complement ns n
            (GetMeasurementBasis (ns - 1) m false × a
             × (GetMeasurementBasis (ns - 1) m false) †)
             × complement n ns (DensityOf P)))))%R.
Proof.
Admitted.

Lemma equal_props: forall n (P: Assertion n) x m v,
PropOf (AssertPreMeas P x v m) = PropOf P.
Proof.
    intros.
    unfold AssertPreMeas, PropOf. auto.
Qed.

Axiom positive_trace: forall n m (U1: Unitary n) 
(U2: Unitary m), 0 <= fst (trace (Mmult U1 U2)).

Theorem fy_measure: forall n x m P, 
    hoare_triple n n (conjunction (AssertPreMeas P x 0%nat m) 
    (AssertPreMeas P x 1%nat m)) <{ x :=meas m }> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    induction st1.
    simpl. lra.
    rewrite conjunction_expectation.
    simpl.
    destruct (beval (mergeMaps (x !-> 0%nat; fst a) (StateOf P)) (PropOf P)) eqn:bev1.
    assert (Hbev1: beval (mergeMaps (fst a) (x !-> 0%nat; StateOf P))
    (PropOf (AssertPreMeas P x 0 m)) = true).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev1.
    rewrite Hbev1.
    destruct (beval (mergeMaps (x !-> 1%nat; fst a) (StateOf P)) (PropOf P)) eqn:bev2.
    assert (Hbev2: beval (mergeMaps (fst a) (x !-> 1%nat; StateOf P))
    (PropOf (AssertPreMeas P x 1 m)) = true).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev2.
    rewrite Hbev2.
    simpl.
    rewrite equal_traces_meas.
    remember (fst (trace
       (complement ns2 n
          (GetMeasurementBasis (ns2 - 1) m true × snd a
           × (GetMeasurementBasis (ns2 - 1) m true) †)
        × complement n ns2 (DensityOf P)))) as r1.
    remember (fst (trace
       (complement ns2 n
          (GetMeasurementBasis (ns2 - 1) m false × snd a
           × (GetMeasurementBasis (ns2 - 1) m false) †)
        × complement n ns2 (DensityOf P)))) as r2.
    rewrite <- Rplus_assoc.
    remember ((r1 + r2)%R) as r3.
    apply Rplus_le_compat_l.
    apply IHst1.
    apply E_Meas.
    assert (Hbev2: beval (mergeMaps (fst a) (x !-> 1%nat; StateOf P))
    (PropOf (AssertPreMeas P x 1 m)) = false).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev2.
    rewrite Hbev2.
    simpl.
    remember (fst (trace
       (complement ns2 n
          (GetMeasurementBasis (ns2 - 1) m true × snd a
           × (GetMeasurementBasis (ns2 - 1) m true) †)
        × complement n ns2 (DensityOf P)))) as r1.
    eapply Rlt_trans_eq.
    apply IHst1.
    apply E_Meas.
    apply Rplus_le_sum_0.
    rewrite Heqr1.
    apply positive_trace.
    assert (Hbev1: beval (mergeMaps (fst a) (x !-> 0%nat; StateOf P))
    (PropOf (AssertPreMeas P x 0 m)) = false).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev1.
    rewrite Hbev1.
    destruct (beval (mergeMaps (x !-> 1%nat; fst a) (StateOf P)) (PropOf P)) eqn:bev2.
    assert (Hbev2: beval (mergeMaps (fst a) (x !-> 1%nat; StateOf P))
    (PropOf (AssertPreMeas P x 1 m)) = true).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev2.
    rewrite Hbev2.
    simpl.
    remember (fst (trace
       (complement ns2 n
          (GetMeasurementBasis (ns2 - 1) m false × snd a
           × (GetMeasurementBasis (ns2 - 1) m false) †)
        × complement n ns2 (DensityOf P)))) as r1.
    eapply Rlt_trans_eq.
    apply IHst1.
    apply E_Meas.
    apply Rplus_le_sum_0.
    rewrite Heqr1.
    apply positive_trace.
    assert (Hbev2: beval (mergeMaps (fst a) (x !-> 1%nat; StateOf P))
    (PropOf (AssertPreMeas P x 1 m)) = false).
    rewrite equal_props.
    rewrite equivalent_with_respect_to_x. apply bev2.
    rewrite Hbev2.
    simpl.
    apply IHst1.
    apply E_Meas.
Qed.

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
  beval (mergeMaps st (StateOf P)) (PropOf P) = true ->
  beval (mergeMaps st (StateOf Q)) (PropOf Q) = true.

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
    destruct (beval (mergeMaps (fst a) (StateOf P)) (PropOf P)) eqn:bev.
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
        else fst (trace (snd a ⊗ I (2^(ns - n)) × DensityOf Q))) +
       Expectation ns n st Q)%R
     else Expectation ns n st Q)).
    destruct (beval (mergeMaps (StateOf Q) (fst a)) (PropOf Q)) eqn:bev2.
    destruct (ns =? n) eqn:nsn.
    apply Rplus_le_sum_0.
    apply positive_trace.
    apply Rplus_le_sum_0.
    apply positive_trace.
    right. reflexivity.
    destruct (beval (mergeMaps (fst a) (StateOf Q)) (PropOf Q)) eqn:bev2.
    assert(Expectation ns n st Q <=
    fst (trace (complement ns n (snd a) × complement n ns (DensityOf Q)))
     + Expectation ns n st Q).
    apply Rplus_le_sum_0.
    apply positive_trace.
    eapply Rlt_trans_eq.
    apply IHst.
    apply H1.
    assert(Expectation ns n st Q <=
    fst (trace (complement ns n (snd a) 
    × complement n ns (DensityOf Q)))
     + Expectation ns n st Q).
    apply Rplus_le_sum_0.
    apply positive_trace.
    eapply Rlt_trans_eq.
    apply IHst.
    right. 
    reflexivity.
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



 