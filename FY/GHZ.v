From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X0 : string := "X0".
Definition X1 : string := "X1".
Definition X2 : string := "X2".

Definition GHZ : com :=
  <{ new_qubit;
     new_qubit;
     new_qubit;
     q 0 *= GH;
     q 0 (*1*) *= GCNOT;
     q 1 (*2*) *= GCNOT;
     X0 :=meas 0;
     X1 :=meas 1;
     X2 :=meas 2;
     skip
    }>.

Print GHZ.

Definition p000 : Unitary (1 * 1 * 1) := 
 (⟨0∣⊗⟨0∣⊗⟨0∣) × (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣
× (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2
   × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2
      × (I 2 ⊗ CNOT
         × (CNOT ⊗ I 2
            × (H ⊗ I 2 ⊗ I 2
               × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
               × (H ⊗ I 2 ⊗ I 2) †) × 
            (CNOT ⊗ I 2) †) × (I 2 ⊗ CNOT) †)
      × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) †) × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2) †)
× (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣) †) × (∣0⟩⊗∣0⟩⊗∣0⟩).

Theorem p000_1: p000 0%nat 0%nat = 1.
Proof.
Admitted.

Theorem final_state: ceval 0%nat 3%nat GHZ [(( _ !-> 0%nat), I 1)] 
[(X2 !-> 0%nat; X1 !-> 0%nat; X0 !-> 0%nat; _ !-> 0%nat, I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣ × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2× (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2× (I 2 ⊗ CNOT× (CNOT ⊗ I 2 × (H ⊗ I 2 ⊗ I 2 × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
               × (H ⊗ I 2 ⊗ I 2) †) × 
            (CNOT ⊗ I 2) †) × (I 2 ⊗ CNOT) †)
      × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) †) × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2) †)
× (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣) †);
(X2 !-> 1%nat; X1 !-> 0%nat; X0 !-> 0%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣
× (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2
  × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣) †);
(X2 !-> 0%nat; X1 !-> 1%nat; X0 !-> 0%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣
× (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2
  × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣) †);
(X2 !-> 1%nat; X1 !-> 1%nat; X0 !-> 0%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣
× (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2
  × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣) †);
(X2 !-> 0%nat; X1 !-> 0%nat; X0 !-> 1%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣
× (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2
  × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣) †);
(X2 !-> 1%nat; X1 !-> 0%nat; X0 !-> 1%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣
× (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2
  × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣0⟩⟨0∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣) †);
(X2 !-> 0%nat; X1 !-> 1%nat; X0 !-> 1%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣
× (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2
  × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣0⟩⟨0∣) †);
(X2 !-> 1%nat; X1 !-> 1%nat; X0 !-> 1%nat; _ !-> 0%nat,
I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣
× (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2
  × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2
     × (I 2 ⊗ CNOT
        × (CNOT ⊗ I 2
           × (H ⊗ I 2 ⊗ I 2
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
              × (H ⊗ I 2 ⊗ I 2) †) × (CNOT ⊗ I 2) †)
        × (I 2 ⊗ CNOT) †) × (∣1⟩⟨1∣ ⊗ I 2 ⊗ I 2) †)
  × (I 2 ⊗ ∣1⟩⟨1∣ ⊗ I 2) †) × (I 2 ⊗ I 2 ⊗ ∣1⟩⟨1∣) †)].
Proof. 
  eapply E_Seq.
  apply E_Init.
  simpl.
  eapply E_Seq.
  apply E_Init.
  simpl.
  eapply E_Seq.
  apply E_Init.
  simpl.
  eapply E_Seq.
  eapply E_AppOne.
  simpl.
  eapply E_Seq.
  eapply E_AppOne.
  simpl.
  eapply E_Seq.
  eapply E_AppOne.
  simpl.
  eapply E_Seq.
  eapply E_Meas.
  simpl.
  eapply E_Seq.
  eapply E_Meas.
  simpl.
  eapply E_Seq.
  eapply E_Meas.
  simpl.
  (*eapply E_Skip.
  simpl.*)
Abort.


(* TODO : Swap gate+no cloning*)
Definition P : Assertion 0 :=  (( _ !-> 0%nat), (<{ true }>, I 1)).
Definition Q : Assertion 3 :=  (( _ !-> 0%nat), (<{ X1 == X2 }>, I 3)).

Lemma H4: (I 2 ⊗ CNOT) × (CNOT ⊗ I 2) × (H ⊗ I 2 ⊗ I 2)
      × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) × (H ⊗ I 2 ⊗ I 2) †
      × (CNOT ⊗ I 2) † × (I 2 ⊗ CNOT) † = l2M [[1/2;0;0;0;0;0;0;1/2];
[0;0;0;0;0;0;0;0];
[0;0;0;0;0;0;0;0];
[0;0;0;0;0;0;0;0];
[0;0;0;0;0;0;0;0];
[0;0;0;0;0;0;0;0];
[0;0;0;0;0;0;0;0];
[1/2;0;0;0;0;0;0;1/2]].
Proof.
(* BY PYTHON SCRIPT *)
Admitted.

Theorem ghz_equality_end: hoare_triple P GHZ Q.
Proof.
  intros.
  eapply fy_sequence.
  replace P with (init_sub 1 (AssertionOf 1 (StateOf P) (PropOf P) (∣0⟩⟨0∣))).
  assert (hoare_triple (init_sub 1 (AssertionOf 1 (StateOf P) (PropOf P) ∣0⟩⟨0∣))
  <{ new_qubit }> (AssertionOf 1 (StateOf P) (PropOf P) (∣0⟩⟨0∣))).
  apply fy_init.
  apply H.
  unfold init_sub, AssertionOf, P, DensityOf, StateOf, PropOf. 
  simpl.
  assert (Hinit: pre_init 1 ∣0⟩⟨0∣ = I 1).
  unfold pre_init, base1, base2. simpl. admit.
  rewrite Hinit.
  reflexivity.
  eapply fy_sequence.
  remember (AssertionOf 1 (StateOf P) (PropOf P) ∣0⟩⟨0∣) as P1.
  replace P1 with (init_sub 2 (AssertionOf 2 (StateOf P) (PropOf P) (∣0⟩⊗ (∣0⟩⟨0∣) ⊗⟨0∣))).
  assert (hoare_triple (init_sub 2 (AssertionOf 2 (StateOf P) (PropOf P) (∣0⟩⊗(∣0⟩⟨0∣)⊗⟨0∣)))
  <{ new_qubit }> (AssertionOf 2 (StateOf P) (PropOf P) (∣0⟩⊗(∣0⟩⟨0∣)⊗⟨0∣))).
  apply fy_init.
  apply H.
  admit.
  eapply fy_sequence.
  remember  (AssertionOf 2 (StateOf P) (PropOf P) (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣)) as P1.
  replace P1 with (init_sub 3 (AssertionOf 3 (StateOf P) (PropOf P) (∣0⟩⊗(∣0⟩⊗ (∣0⟩⟨0∣) ⊗⟨0∣)⊗⟨0∣))).
  assert (hoare_triple (init_sub 3 
  (AssertionOf 3 (StateOf P) (PropOf P) 
  (∣0⟩⊗(∣0⟩⊗ (∣0⟩⟨0∣) ⊗⟨0∣)⊗⟨0∣)))
  <{ new_qubit }>  
  (AssertionOf 3 (StateOf P) (PropOf P) (∣0⟩⊗(∣0⟩⊗ (∣0⟩⟨0∣) ⊗⟨0∣)⊗⟨0∣))).
  apply fy_init.
  apply H.
  admit.
  eapply fy_sequence.
  remember  (AssertionOf 3 (StateOf P) (PropOf P) 
    (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)) as P1.
  replace P1 with (apply_sub 3%nat 0%nat Utils.H true 
    (AssertionOf 3%nat (StateOf P) (PropOf P)
     ((padding 2 0 Utils.H) 
        × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
          × (padding 2 0 Utils.H)†)) ).
  assert (hoare_triple
      (apply_sub 3%nat 0%nat Utils.H true
         (AssertionOf 3%nat (StateOf P) (PropOf P)
            ((padding 2 0 Utils.H) 
               × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                  × (padding 2 0 Utils.H)†)) )
      <{ q 0 *= GH }> 
      (AssertionOf 3%nat (StateOf P) (PropOf P)
            ((padding 2 0 Utils.H) 
               × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                  × (padding 2 0 Utils.H)†))
  ).
  apply fy_apply.
  apply H.
  admit.
  eapply fy_sequence.
  remember (AssertionOf 3 (StateOf P) (PropOf P)
  (padding 2 0 H × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣)
   × (padding 2 0 H) †)) as P1.
  replace P1 with (apply_sub 3%nat 0%nat Utils.CNOT false
    (AssertionOf 3%nat (StateOf P) (PropOf P)
     ((padding4 1 0 Utils.CNOT) 
         × (padding 2 0 Utils.H) 
            × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
               × (padding 2 0 Utils.H)† 
                  × (padding4 1 0 Utils.CNOT)†)) ).
  assert (hoare_triple 
      (apply_sub 3%nat 0%nat Utils.CNOT false
         (AssertionOf 3%nat (StateOf P) (PropOf P)
            ((padding4 1 0 Utils.CNOT) 
               × (padding 2 0 Utils.H) 
                  × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                     × (padding 2 0 Utils.H)† 
                  × (padding4 1 0 Utils.CNOT)†)) )
      <{ q 0 (*1*) *= GCNOT }> 
      (AssertionOf 3%nat (StateOf P) (PropOf P)
            ((padding4 1 0 Utils.CNOT) 
               × (padding 2 0 Utils.H) 
                  × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                     × (padding 2 0 Utils.H)† 
                  × (padding4 1 0 Utils.CNOT)†))).
  apply fy_apply.
  apply H.
  admit.
  eapply fy_sequence.
  remember (AssertionOf 3 (StateOf P) (PropOf P)
  ((padding4 1 0 CNOT) × (padding 2 0 H)
   × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) × (padding 2 0 H) †
   × (padding4 1 0 CNOT) †)) as P1.
  replace P1 with (apply_sub 3%nat 1%nat Utils.CNOT false
    (AssertionOf 3%nat (StateOf P) (PropOf P)
     ((padding4 1 1 Utils.CNOT) 
      × (padding4 1 0 Utils.CNOT) 
         × (padding 2 0 Utils.H) 
            × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
               × (padding 2 0 Utils.H)† 
                  × (padding4 1 0 Utils.CNOT)†
                     × (padding4 1 1 Utils.CNOT)†)) ).
  assert (hoare_triple 
      (apply_sub 3%nat 1%nat Utils.CNOT false
      (AssertionOf 3%nat (StateOf P) (PropOf P)
       ((padding4 1 1 Utils.CNOT) 
        × (padding4 1 0 Utils.CNOT) 
           × (padding 2 0 Utils.H) 
              × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                 × (padding 2 0 Utils.H)† 
                    × (padding4 1 0 Utils.CNOT)†
                       × (padding4 1 1 Utils.CNOT)†)) )
      <{ q 1 *= GCNOT }> 
      (AssertionOf 3%nat (StateOf P) (PropOf P)
      ((padding4 1 1 Utils.CNOT) 
       × (padding4 1 0 Utils.CNOT) 
          × (padding 2 0 Utils.H) 
             × (∣ 0 ⟩ ⊗ (∣ 0 ⟩ ⊗ ∣0⟩⟨0∣ ⊗ ⟨0∣) ⊗ ⟨0∣) 
                × (padding 2 0 Utils.H)† 
                   × (padding4 1 0 Utils.CNOT)†
                      × (padding4 1 1 Utils.CNOT)†))).
  apply fy_apply.
  apply H.
  admit.
  unfold padding. simpl. 
  (* rewrite H4. *)
Abort.








