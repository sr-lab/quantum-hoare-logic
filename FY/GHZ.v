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
     q 0 1 *= GCNOT;
     q 1 2 *= GCNOT;
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
  eapply E_AppTwo.
  simpl.
  eapply E_Seq.
  eapply E_AppTwo.
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
Definition P (tm: total_map nat): Assertion 3 :=  fun st => (<{ true }>, I 0).
Definition Q (tm: total_map nat): Assertion 3 :=  fun st => (<{ X1 == X2 }>, I 3).

Theorem ghz_equality_end: forall tm, hoare_triple 0 3 (P tm) GHZ (Q tm).
Proof.
  intros.
  eapply fy_sequence.
Abort.








