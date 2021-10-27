From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X : string := "X".
Definition Y0 : string := "Y0".
Definition Y1 : string := "Y1".
Definition K : string := "K".

Lemma kron_I_1: kron (I 2) (I 1) == I 2.
Proof.
  lma.
Qed.

Definition GROVER : com :=
  <{
    new_qubit;
    new_qubit;
    q 0 *= GH;
    q 1 *= GH;
    (*Oracle - start*)
    q 0 *= GH;
    q 1 *= GH;
    q 0 *= GZ;
    q 1 *= GZ;
    (*Oracle - end*)
    K := (2 % nat); (* 3 ~ sqrt(8) *)
    X := (0 % nat);
    while X <= K do
      q 0 1 *= GCNOT;
      X := (X + 1%nat)
    end;
    Y0 :=meas 0;
    Y1 :=meas 1
  }>.

Print GROVER.

Theorem final_state: ceval 0%nat 3%nat GROVER [(( _ !-> 0%nat), I 1)] 
[(( X !-> 2%nat ; K !-> 2%nat ; 
    Y0 !-> 0%nat ;
    Y1 !-> 0%nat ; _ !-> 0%nat), ∣0⟩⟨0∣ )] .
Proof.
  eapply E_Seq.
  apply E_Init.
  eapply E_Seq.
  apply E_Init.
  eapply E_Seq.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_AppOne.
  eapply E_Seq.
  simpl.
  apply E_Ass.
  eapply E_Seq.
  simpl.
  apply E_Ass.
  eapply E_Seq.
  simpl.
  eapply E_WhileTrue.
  (* there is a problem *)
Admitted.





