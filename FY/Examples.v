From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.

Definition X : string := "X".
Definition Y : string := "Y".

Check <{ X + (3 % nat) }>.

Example aexp1 :
    aeval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ X + (3 % nat) - Y }> = 5%nat.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5%nat; Y !-> 3%nat ; _ !-> 0%nat) <{ Y <= X }> = true.
Proof. reflexivity. Qed.

Check H.

Example state1:
  ApplyOneQubitGate 0%nat 0%nat H = H.
Proof.
  reflexivity.
Qed.

Example state2:
  ApplyOneQubitGate 0%nat 0%nat CNOT = CNOT.
Proof.
  reflexivity.
Qed.

Example state3:
  ApplyOneQubitGate 1%nat 0%nat H = H.
Proof.
Admitted.

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
  rewrite Cplus_0_l.
Admitted.


Example expect: (Expectation 2 2 [((X !-> 0%nat; _ !-> 1%nat), H)] assert) = 1.
Proof.
  simpl.
  rewrite HI0.
  rewrite SC0.
  (*There is a problem here*)
  (*rewrite HHI.
  auto.*)
Qed.


Definition Prog1 : com :=
  <{ q 0 := 0;
     q 0 *= GH;
     X :=measQ 0 }>.
Print Prog1.

Theorem state_eval_1: ceval Prog1 [((_ !-> 0%nat), I 0)] [((X !-> 0%nat ; _ !-> 1%nat), H) ; ((X !-> 1%nat; _ !-> 1%nat), H)].
Proof.
  eapply E_Seq.
  apply E_Init.
  eapply E_Seq.
  apply E_AppOne.
Admitted.


(* ENONTRA BOM EXEMPLOS PARA APRESENTAÇÃO*)
(* () -> ∣0⟩⟨0∣ . I *)
(* 
(X -> 0) ->  1/sqrt(2)[[1, -1], [1, 1]]
(X -> 1) ->  1/sqrt(2)[[1, -1], [1, 1]]

() -> (X < 0.5) * (I 2)
*)

Definition Prog2 : com :=
  <{ q 0 := 0;
     q 0 *= GH;
     X :=measQ 0%nat;
     if false then
        q 0 *= GZ
     else
        skip
    end }>.
Print Prog2.

Definition Prog3 : com :=
  <{ q 0 := 0;
     q 0 *= GH }>.

Theorem state_eval_3: ceval Prog3 [((_ !-> 0%nat), I 2)] [((_ !-> 0%nat), H ⊗ ∣0⟩⟨0∣ ⊗ H†)].
Proof.
  eapply E_Seq.
  - apply E_Init.
  - unfold UpdateStateInit. simpl.
Admitted.

Definition Prog4 : com :=
  <{ q 0%nat := 0 }>.

Definition Prog5 : com :=
  <{ X :=c (2 % nat);
    q 0 := 0;
    if X == (2 % nat) then
       q 0 *= GH
    else
       q 0 *= GX
    end}>.

Theorem state_eval_5: ceval Prog5 [((_ !-> 0%nat), I 2%nat)] [((X !-> 2%nat; _ !-> 0%nat), H × ∣0⟩⟨0∣ × H†)].
Proof.
  eapply E_Seq.
  apply E_Ass.
  eapply E_Seq.
  apply E_Init.
  apply E_IfFalse.
  simpl.
  (* there is a problem here*)
  (* eapply E_AppOne. *)
Abort.






