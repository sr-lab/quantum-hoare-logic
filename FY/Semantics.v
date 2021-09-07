From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export State.
Import ListNotations.

Inductive ceval {nq}: com -> list ((total_map nat)*(Unitary nq)) -> list ((total_map nat)*(Unitary nq)) -> Prop :=
  | E_Skip : forall st,
      ceval <{ skip }> st st
  | E_Ass : forall st a x,
      ceval <{ x :=c a }> st (UpdateStateAssign nq st x a)
  | E_Init : forall m st,
      ceval <{ q m := 0 }> st (UpdateStateInit nq st m)
  | E_App : forall st U m,
      ceval <{ q m *= U }> st (UpdateStateApply nq st m U)
  | E_Meas : forall st x m,
      ceval <{ x :=measQ m }> st (UpdateStateMeasure nq st x m)
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval <{ c1 ; c2 }> st st''
  | E_IfTrue : forall st st' b c1 c2,
      ceval c1 (Filter nq st b) st' ->
      ceval <{ if b then c1 else c2 end }> st st'
  | E_IfFalse : forall st st' b c1 c2,
      ceval c2 (FilterNeg nq st b) st' ->
      ceval <{ if b then c1 else c2 end }> st st'
  | E_WhileTrue : forall st st' st'' b c,
      ceval c (Filter nq st b) st' ->
      ceval <{ while b do c end }> (Filter nq st b) st' ->
      ceval <{ while b do c end }> st' st''
  | E_WhileFalse : forall st b c,
      ceval <{ while b do c end }> (FilterNeg nq st b) (FilterNeg nq st b).
