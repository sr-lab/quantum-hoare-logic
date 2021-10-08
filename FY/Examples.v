From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.

Definition X : string := "X".
Definition Y : string := "Y".

Example aexp1 :
    aeval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ X + (3 % nat) - Y }> = 5%nat.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ Y <= X }> = true.
Proof. reflexivity. Qed.

Example state1:
  padding 2%nat 0%nat H = I 2 ⊗ (I 2 ⊗ H).
Proof.
  reflexivity.
Qed.

Example state2:
  padding 2%nat 1%nat H = I 2 ⊗ (H ⊗ I 2).
Proof.
  reflexivity.
Qed.

Example state3:
padding 0%nat 0%nat CNOT = CNOT.
Proof.
  reflexivity.
Qed.

Example state4:
padding 1%nat 0%nat H = I 2 ⊗ H.
Proof.
  reflexivity.
Qed.


Definition assert : Assertion 2 := fun (tmn: total_map nat) => pair <{ X <= (2 % nat) }> H.

Example satisfied: beval (X !-> 0%nat; _ !-> 1%nat) (fst (assert (X !-> 0%nat; _ !-> 1%nat))) = true.
Proof. auto. Qed.

Lemma HI0 : H ⊗ I 0 = H.
Proof.
Admitted.

Lemma SC0 : forall (c : C), Cplus c 0 = c.
Proof.
Admitted.

Lemma HHI : trace (H × H) = 1. 
Proof.
  unfold trace.
  unfold H.
  unfold Mmult.
  simpl.
  unfold Cplus.
  simpl.
Admitted.


Example expect: (Expectation 2 2 [((X !-> 0%nat; _ !-> 1%nat), H)] assert) = 1.
Proof.
  simpl.
  rewrite HI0.
  rewrite SC0.
  (*There is a problem here*)
  (*rewrite HHI.
  auto.*)
Admitted.


Definition Prog1 : com :=
  <{ new_qubit;
    q 0 *= GH;
     X :=meas 0;
     skip
  }>.
Print Prog1.

Check ∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣) †.

Theorem state_eval_1: ceval 0%nat 1%nat Prog1
 [((_ !-> 0%nat), I 0)] 
 [(X !-> 0%nat; _ !-> 0%nat, ∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣) †);
 (X !-> 1%nat; _ !-> 0%nat, ∣1⟩⟨1∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣1⟩⟨1∣) †)].
Proof.
  eapply E_Seq.
  eapply E_Init.
  simpl.
  eapply E_Seq.
  apply E_AppOne.
  simpl.
  eapply E_Seq.
  apply E_Meas.
  simpl.
  apply E_Skip.
Qed.
(* ENONTRA BOM EXEMPLOS PARA APRESENTAÇÃO*)
(* () -> ∣0⟩⟨0∣ . I *)
(* 
(X -> 0) ->  1/sqrt(2)[[1, -1], [1, 1]]
(X -> 1) ->  1/sqrt(2)[[1, -1], [1, 1]]

() -> (X < 0.5) * (I 2)
*)

Definition Prog2 : com :=
  <{ new_qubit;
     q 0 *= GH;
     X :=meas 0%nat;
     if false then
        q 0 *= GZ
     else
        skip
    end }>.
Print Prog2.

Definition Prog3 : com :=
  <{ new_qubit;
     q 0 *= GH }>.

Theorem state_eval_3: ceval 0%nat 1%nat Prog3 [((_ !-> 0%nat), I 2)] [((_ !-> 0%nat), H × ∣0⟩⟨0∣ × H†)].
Proof.
  eapply E_Seq.
  apply E_Init.
  simpl.
  apply E_AppOne.
Qed.

Definition Prog4 : com :=
  <{ new_qubit }>.

Definition Prog5 : com :=
  <{
    new_qubit; 
    X := (2 % nat);
    if X == (2 % nat) then
       q 0 *= GH
    else
       q 0 *= GX
    end}>.

Theorem state_eval_5: ceval 0%nat 1%nat Prog5 [((_ !-> 0%nat), I 1%nat)] [((X !-> 2%nat; _ !-> 0%nat), H × ∣0⟩⟨0∣ × H†)].
Proof.
  eapply E_Seq.
  eapply E_Init.
  simpl.
  eapply E_Seq.
  eapply E_Ass.
  simpl.
  apply E_IfTrue.
  simpl.
  eapply E_AppOne.
Qed.





