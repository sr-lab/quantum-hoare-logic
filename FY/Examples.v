From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.


Definition X : string := "X".

Definition Prog1 : com :=
  <{ q 0 := 0;
     q 0 *= GH;
     X :=measQ 0%nat }>.
Print Prog1.

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
     if BEq X 2%nat then
        q 0 *= GZ
    else
        skip
    end }>.
Print Prog2.

Definition Prog3 : com :=
  <{ q 0 := 0;
     q 0 *= GH }>.


Definition Prog4 : com :=
  <{ q 0%nat := 0 }>.

Definition zero := 0%nat.

Definition Prog5 : com :=
  <{ X :=c APlus 0%nat 1%nat }>.

Theorem state_eval_1: ceval Prog1 [((_ !-> 0%nat), I 2)] [((X !-> 0%nat ; _ !-> 1%nat), H) ; ((X !-> 1%nat; _ !-> 1%nat), H)].
Proof.
  eapply E_Seq.
  apply E_Init.
  eapply E_Seq.
  apply E_App.
  apply E_Meas.
  apply E_Seq with [((X !-> 0%nat ; _ !-> 0%nat), H) ; ((X !-> 1%nat; _ !-> 0%nat), H)].

Admitted.


Theorem state_eval_3: ceval <{ q 0%nat := 0 }> [((_ !-> 0%nat), I 2)] [((_ !-> 0%nat), ∣0⟩⟨0∣)].
Proof.
Admitted.



