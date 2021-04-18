From FY Require Import Semantics.
From FY Require Import Matrix.
Require Import List.
Import ListNotations.
From FY Require Import Map.
From FY Require Import Complex.
From Coq Require Import Lia.
From Coq Require Import Strings.String.

Definition State {n: nat} := total_map nat -> Matrix n n.

Definition Assertion {n: nat} := total_map nat -> Matrix n n.

Fixpoint Expectation (sts: list (total_map nat)) (d : State)
 (th : Assertion) : C := 
  match sts with
  | nil => 0
  | st::tail => trace (Mmult (d st) (th st)) + Expectation tail d th 
  end.




