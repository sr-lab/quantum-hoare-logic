From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Sets.Ensembles.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export State.
Import ListNotations.

Inductive ceval : nat -> nat -> com 
    -> list ((total_map nat)*(Unitary 1%nat))
    -> list ((total_map nat)*(Unitary 1%nat)) 
    -> Prop :=
  | E_Skip : forall n st,
      ceval n n <{ skip }> st st
  | E_Ass : forall n st a x,
      ceval n n <{ x := a }> st (UpdateStateAssign n st x a)
  | E_Init : forall n st,
      ceval n (n + 1%nat) <{ new_qubit }> st (UpdateStateInit n st)
  | E_AppOne : forall n st U m,
      ceval n n <{ q m *= U }> st (UpdateStateApply n st m U)
  | E_AppTwo : forall n st U m r,
      ceval n n <{ q m r *= U }> st (UpdateStateApply n st m U)
  | E_Meas : forall n st x m,
      ceval n n <{ x :=meas m }> st (UpdateStateMeasure n st x m)
  | E_Seq : forall n n' n'' c1 c2 st st' st'',
      ceval n n' c1 st st' ->
      ceval n' n'' c2 st' st'' ->
      ceval n n'' <{ c1 ; c2 }> st st''
  | E_If : forall n n' st st' st'' b c1 c2,
      ceval n n' c1 (Filter n st b) st' ->
      ceval n n' c2 (Filter n st (BNot b)) st'' ->
      ceval n n' <{ if b then c1 else c2 end }> st (st' ++ st'')
  | E_WhileTrue : forall n n' st st' st'' b c,
      ceval n n' c (Filter n st b) st' ->
      ceval n n' <{ while b do c end }> (Filter n st b) st' ->
      ceval n n' <{ while b do c end }> st' st''
  | E_WhileFalse : forall n n' st b c,
      ceval n n' <{ while b do c end }> (FilterNeg n st b) (FilterNeg n st b).
