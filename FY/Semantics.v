From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY2 Require Export Utils.
From FY2 Require Export Syntax.
Import ListNotations.
(* variables register, 1 for classic, 2 for quantum *)

Notation register := (total_map nat).

Notation cstate := (total_map nat).

Notation qstate := (total_map (Vector 2)).

Fixpoint aeval (cst : cstate)
        (a : arith_exp) : nat :=
  match a with
  | ANum m => m
  | ACId x => cst x
  | <{a1 + a2}> => (aeval cst a1) + (aeval cst a2)
  | <{a1 - a2}> => (aeval cst a1) - (aeval cst a2)
  | <{a1 * a2}> => (aeval cst a1) * (aeval cst a2)
  | <{a1 / a2}> => (aeval cst a1) / (aeval cst a2)
  end.

Fixpoint beval (cst : cstate) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval cst a1) =? (aeval cst a2)
  | <{a1 <= a2}> => (aeval cst a1) <=? (aeval cst a2)
  | <{~ b1}> => negb (beval cst b1)
  | <{b1 && b2}> => andb (beval cst b1) (beval cst b2)
  end.

Fixpoint qeval (qst : qstate) (q : quantum_exp) : Vector 2 :=
  match q with
  | AQId x => qst x
  end.

Definition geval (g : gate_exp) : Unitary 2 :=
  match g with
  | GI => I 2
  | GH => H
  | GX => X
  | GZ => Z
  | GY => Y
  end.

Inductive ceval : com -> cstate -> qstate -> cstate -> qstate -> Prop :=
  | E_Skip : forall cst qst,
      ceval <{ skip }> cst qst cst qst
  | E_Ass : forall cst qst a m x,
      aeval cst a = m ->
      ceval <{ x :=c a }> cst qst (x !-> m; cst) qst
  | E_Init : forall q cst (qst : qstate),
      ceval <{ q :=q 0 }> cst qst cst (q !-> ∣0⟩; qst)
  | E_App : forall cst qst U q,
      ceval <{ q *= U }> cst qst cst (q !-> ((geval U) × (qst q)); qst)
  | E_Meas0 : forall cst qst x q,
      ceval <{ x :=meas q }> cst qst (x !-> 0%nat ; cst) (q !-> ∣0⟩; qst)
  | E_Meas1 : forall cst qst x q,
      ceval <{ x :=meas q }> cst qst (x !-> 1%nat ; cst) (q !-> ∣1⟩; qst)
  | E_Seq : forall c1 c2 cst qst cst' qst' cst'' qst'',
      ceval c1 cst qst cst' qst' ->
      ceval c2 cst' qst' cst'' qst'' ->
      ceval <{ c1 ; c2 }> cst qst cst'' qst''
  | E_IfTrue : forall  cst qst cst' qst' b c1 c2,
      beval cst b = true ->
      ceval c1 cst qst cst' qst' ->
      ceval <{ if b then c1 else c2 end }> cst qst cst' qst'
  | E_IfFalse : forall cst qst cst' qst' b c1 c2,
      beval cst b = false ->
      ceval c2 cst qst cst' qst' ->
      ceval <{ if b then c1 else c2 end }> cst qst cst' qst'
  | E_WhileFalse : forall cst qst b c,
      beval cst b = false ->
      ceval <{ while b do c end }> cst qst cst qst 
  | E_WhileTrue : forall cst qst cst' qst' cst'' qst'' b c,
      beval cst b = true ->
      ceval c cst qst cst' qst' ->
      ceval <{ while b do c end }> cst qst cst' qst' ->
      ceval <{ while b do c end }> cst' qst' cst'' qst''.










