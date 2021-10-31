From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X : string := "X".
Definition Y : string := "Y".

Example pad1:
padding4 1 1 CNOT = I 2 ⊗ CNOT.
Proof.
  unfold padding4.
  Check (padding4 2 0 CNOT).
  simpl.
  reflexivity.
Qed.

Example aexp1 :
    aeval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ X + (3 % nat) - Y }> = 5%nat.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ Y <= X }> = true.
Proof. reflexivity. Qed.

Example state1:
  padding 2%nat 0%nat H = H ⊗ (I 2) ⊗ (I 2).
Proof.
  simpl.
  reflexivity.
Qed.

Example state2:
  padding 2%nat 1%nat H = I 2 ⊗ H ⊗ I 2.
Proof.
  reflexivity.
Qed.

Example state3:
padding 0%nat 0%nat CNOT = CNOT.
Proof.
  reflexivity.
Qed.

Example state4:
padding 1%nat 0%nat H = H ⊗ I 2.
Proof.
  reflexivity.
Qed.

Example state5:
GetMeasurementBasis 1%nat 1%nat true = I 2 ⊗ ∣0⟩⟨0∣.
Proof.
  simpl.
  reflexivity.
Qed.

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
Admitted.

Definition assert2 : Assertion 2 := pair (_ !-> 0%nat) (pair <{ X <= (3 % nat) }> H).

Definition st2 := [(X !-> 1%nat; _ !-> 0%nat, H)].

Example expect: (Expectation 2 2 st2 (assert2)) = 2%R.
Proof.
  simpl.
  repeat (
  try field_simplify ;
  try rewrite pow2_sqrt;
  try rewrite pown_sqrt;
  try lra;
  try apply sqrt_neq_0_compat).
Qed.

Definition Prog1 : com :=
  <{ new_qubit;
    q 0 *= GH;
     X :=meas 0;
     skip
  }>.
Print Prog1.
 
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

Example props: (⟨0∣ × (∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣) †) × ∣0⟩) 0%nat 0%nat = 1.
Proof.
  unfold H, Mmult, qubit0, qubit1, adjoint; simpl.
  C_field_simplify; simpl.
  rewrite Cconj_R.
  field_simplify.
  rewrite Cconj_R.
  field_simplify.
  rewrite Cconj_rad2.
  rewrite Cplus_0_l.
  field_simplify.
  unfold Cmult.
  simpl.
  rewrite Cplus_0_l.
  rewrite Rmult_0_r.
  rewrite Rmult_1_r.
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  rewrite Rplus_0_r.
  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  unfold Cplus.
  simpl.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  rewrite Rplus_0_r.
  unfold RtoC.
  unfold Cdiv.
Admitted.
(* ENONTRA BOM EXEMPLOS PARA APRESENTAÇÃO*)
(* () -> ∣0⟩⟨0∣ . I *)
(* 
(X -> 0) ->  1/sqrt(2)[[1, -1], [1, 1]]
(X -> 1) ->  1/sqrt(2)[[1, -1], [1, 1]]

() -> (X < 0.5) * (I 2)
*)

Example Prog2 : com :=
  <{ new_qubit;
     new_qubit;
     q 0 *= GH;
     X :=meas 0%nat;
     if X == (0 % nat) then
        q 1 *= GX
     else
        skip
     end;
     Y :=meas 1%nat   
  }>.
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
    end;
    Y :=meas 0
    }>.

Theorem matrix_1: ∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣) † = l2M [[1;0];[0;0]].
Proof.
Admitted.


Theorem state_eval_5: ceval 0%nat 1%nat Prog5 [((_ !-> 0%nat), I 1%nat)] 
[(Y !-> 0%nat; X !-> 2%nat; _ !-> 0%nat, ∣0⟩⟨0∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣0⟩⟨0∣) †);
 (Y !-> 1%nat; X !-> 2%nat; _ !-> 0%nat, ∣1⟩⟨1∣ × (H × ∣0⟩⟨0∣ × (H) †) × (∣1⟩⟨1∣) †)].
Proof.
  eapply E_Seq.
  eapply E_Init.
  simpl.
  eapply E_Seq.
  eapply E_Ass.
  simpl.
  eapply E_Seq.
  apply E_If.
  simpl.
  eapply E_AppOne.
  simpl.
  eapply E_AppOne.
  simpl.
  eapply E_Meas.
Qed.

Theorem order: forall a b c: nat, (a <=? b) = true -> (b <=? c) = true -> (a <=? c) = true.
Proof.
Admitted.

Theorem mergeMapsExample: mergeMaps (X !-> 2%nat; _ !-> 0%nat) 
(X !-> 3%nat; Y !-> 1%nat; _ !-> 0%nat) X = 2%nat.
Proof.
    unfold mergeMaps.
    simpl.
    reflexivity.
Qed.

