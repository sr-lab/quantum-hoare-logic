From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X : string := "X".

Definition Prog : com :=
  <{ new_qubit;
     q 0 *= GH;
     X :=meas 0
    }>.

Print Prog.

Fact calc_0: 0.5 * ∣0⟩⟨0∣ = ∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣)†.
Proof. Admitted.

Fact calc_1: 0.5 * ∣1⟩⟨1∣ = ∣1⟩⟨1∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣1⟩⟨1∣)†.
Proof. Admitted.

Theorem operational_sem: 
  ceval 0%nat 1%nat Prog [(( _ !-> 0%nat), I 1)] 
  [(( X !-> 0%nat; _ !-> 0%nat), 0.5 * ∣0⟩⟨0∣ );
   (( X !-> 1%nat; _ !-> 0%nat), 0.5 * ∣1⟩⟨1∣ )].
Proof.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    rewrite calc_0.
    rewrite calc_1.
    eapply E_Meas.
Qed.

Definition pre : Assertion 0%nat := ((_ !-> 0%nat), (BTrue, I 1)).
Definition post : Assertion 1%nat := ((_ !-> 0%nat), (<{ X == (0 % nat)}>, 0.5 * ∣0⟩⟨0∣)).

Lemma pre_is_init_sub: pre = (init_sub 1 (AssertionOf 1%nat (StateOf pre) (PropOf pre) (∣0⟩⟨0∣))).
Proof. Admitted.

Lemma assrt_is_apply_sub: 
(AssertionOf 1 (StateOf pre) (PropOf pre) ∣0⟩⟨0∣)
= (apply_sub 1 (geval GH) 
(AssertionOf 1 (StateOf pre) (PropOf pre) (H × ∣0⟩⟨0∣ × (H) †))) .
Proof. Admitted.

Theorem prog_correct: hoare_triple pre Prog post.
Proof.
    eapply fy_sequence.
    rewrite pre_is_init_sub.
    assert (H1: hoare_triple (init_sub 1%nat (StateOf pre, (PropOf pre, ∣0⟩⟨0∣))) 
    <{ new_qubit }> (AssertionOf 1%nat (StateOf pre) (PropOf pre) ∣0⟩⟨0∣)).
    apply fy_init.
    apply H1.
    eapply fy_sequence.
    assert (H2: hoare_triple (apply_sub 1 (geval GH) 
    (AssertionOf 1 (StateOf pre) (PropOf pre) (H × ∣0⟩⟨0∣ × (H) †))) 
    <{ q 0 *= GH }> (AssertionOf 1 (StateOf pre) (PropOf pre) (Utils.H × ∣0⟩⟨0∣ × Utils.H†))).
    apply fy_apply.
    rewrite assrt_is_apply_sub.
    apply H2.
    eapply fy_weakness.
    remember (AssertionOf 1%nat (_ !-> 0%nat)
      <{ X == (0 % nat) }> (H × ∣0⟩⟨0∣ × (H) †)) as pm.
    assert (H8: hoare_triple (conjunction 
        (AssertPreMeas (AssertionOf 1%nat (_ !-> 0%nat)
        <{ X == (0 % nat) }> (H × ∣0⟩⟨0∣ × (H) †)) X 0%nat 0%nat) 
        (AssertPreMeas (AssertionOf 1%nat (_ !-> 0%nat)
        <{ X == (0 % nat) }> (H × ∣0⟩⟨0∣ × (H) †)) X 1%nat 0%nat))  
        <{ X :=meas 0 }> 
        (AssertionOf 1%nat (_ !-> 0%nat)
        <{ X == (0 % nat) }> (H × ∣0⟩⟨0∣ × (H) †))).
    apply fy_measure.
    apply H8.
    intros.
    unfold weaker, AssertionWithDensity, conjunction,
     AssertPreMeas, AssertionOf.
    simpl.
    unfold PropOf, DensityOf, StateOf.
    simpl.
    induction st.
    simpl.
    lra.
    simpl.
    destruct (mergeMaps (fst a) (_ !-> 0%nat) X =? 0) eqn:bv1.
    simpl.
    admit.
    admit.
    admit.
Admitted.
 