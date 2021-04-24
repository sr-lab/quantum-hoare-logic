From FY Require Import Semantics.
 
Require Import List.
Import ListNotations.
From FY Require Import Map.
From FY Require Import Complex.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From FY Require Export Syntax.

Definition cstate := total_map nat.

Definition qstate (n : nat) := Matrix n n.

Definition Assertion (n: nat) := total_map nat -> Matrix n n.

Fixpoint Expectation {n : nat} (sts: list (total_map nat)) (cst : cstate) (qst : qstate n)
 (th : Assertion n) : C := 
  match sts with
  | nil => 0
  | st::tail => trace (Mmult qst (th cst)) + Expectation tail cst qst th 
  end.

 




