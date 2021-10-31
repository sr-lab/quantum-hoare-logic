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

Definition TELEPORT : com :=
  <{ 
     q 1 *= GH;
     q 1 2 *= GCNOT;
     q 0 1 *= GCNOT;
     q 0 *= GH;
     X0 :=meas 0;
     X1 :=meas 1;
     if X0 == (0 % nat)
     then 
       if X1 == (1 % nat) then q 2 *= GX else skip end 
     else
       if X1 == (1 % nat) then q 2 *= GX; q 2 *= GZ else q 2 *= GZ end 
     end
  }>.

Print TELEPORT.

Definition initial_state (a b: R) := (∣0⟩ ⊗ ∣0⟩ ⊗ (a * ∣0⟩ + b * ∣1⟩)) × ((a^* * ⟨1∣ + b^* * ⟨1∣) ⊗ ⟨0∣ ⊗ ⟨0∣).

Fixpoint satisfied_by_all_elements (n: nat) (state: State n) 
  (P: bool_exp) : bool := match state with
  | [] => true
  | el :: st => andb (beval (fst el) P) (satisfied_by_all_elements n st P)
  end.


Theorem final_state: forall (a b: R),
ceval 3 3 TELEPORT 
[(( _ !-> 0%nat), (initial_state a b)) ] [] .
Proof.
  intros.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    eapply E_Seq.
    simpl.
    apply E_AppTwo.
    simpl.
    eapply E_Seq.
    apply E_AppTwo.
    simpl.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    eapply E_Seq.
    apply E_Meas.
    simpl.
    eapply E_Seq.
    apply E_Meas.
    simpl.
Admitted.

