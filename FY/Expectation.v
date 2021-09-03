From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export State.
From Coq Require Import Strings.String.
Import ListNotations.

Fixpoint Expectation {n : nat}  (state: list ((total_map nat)*(Unitary n))) (b : bool_exp) : C :=
    match state with
        | [] => 0
        | st :: l => if (beval (fst st) b) then Cplus (trace (snd st)) (Expectation l b) else (Expectation l b)
    end.



