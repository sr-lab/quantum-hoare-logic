From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition GROVER : com :=
  <{}>.

Print GROVER.

Theorem final_state: ceval GROVER [(( _ !-> 0%nat), I 1)] [(( _ !-> 0%nat), I 1)] .
Proof.
Admitted.




