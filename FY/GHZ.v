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
  <{ q 0 := 0;
     q 1 := 0;
     q 2 := 0;
     q 0 *=1 GH;
     q 0 1 *=2 GCNOT;
     q 1 2 *=2 GCNOT;
     X0 :=measQ 0;
     X1 :=measQ 1;
     X2 :=measQ 2 }>.

Print GHZ.

Theorem final_state: ceval GHZ [(( _ !-> 0%nat), I 1)] 
  [(( X0 !-> 0%nat; X1 !-> 0%nat; X2 !-> 0%nat; _ !-> 0%nat), I 3); 
   (( X0 !-> 1%nat; X1 !-> 1%nat; X2 !-> 1%nat; _ !-> 0%nat), I 3)].
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
  apply E_AppOne.
  simpl.
  eapply E_Seq.
  apply E_AppTwo.
  simpl.
  eapply E_Seq.
  apply E_AppTwo.
  simpl.
  eapply E_Seq.
  apply E_Meas.
  simpl.
  eapply E_Seq.
  apply E_Meas.
  simpl.
Abort.

(* TODO : Swap gate+no cloning*)
Definition P (tm: total_map nat): Assertion 3 := fun tm => (<{ true }>, I 0).
Definition Q (tm: total_map nat): Assertion 3 := fun tm => (<{ X1 == X2 }>, I 3).

Theorem ghz_equality_end: forall tm, hoare_triple 0 3 (P tm) GHZ (Q tm).
Proof.
  intros.
  eapply fy_sequence.
Abort.







