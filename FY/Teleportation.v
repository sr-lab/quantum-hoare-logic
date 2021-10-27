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
     new_qubit;
     new_qubit;
     q 1 *= GH;
     new_qubit;
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

Theorem final_state: ceval 0%nat 3%nat TELEPORT 
[(( _ !-> 0%nat), I 1) ] [(( _ !-> 0%nat), I 1)] .
Proof.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    eapply E_Seq.
    simpl.
    apply E_Init.
    simpl.
    eapply E_Seq.
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

