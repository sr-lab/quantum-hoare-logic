From FY Require Export Map.
From FY Require Import Matrix. 
From FY Require Export Syntax.
From FY Require Export Quantum.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.


Notation cstate := (total_map nat).

Notation qstate n := (Matrix n n).

Fixpoint aeval {n : nat} (cst : cstate) (qst : qstate n) (a : arith_exp) : nat :=
  match a with
  | ANum m => m
  | AId x => cst x
  | <{a1 + a2}> => (aeval cst qst a1) + (aeval cst qst a2)
  | <{a1 - a2}> => (aeval cst qst a1) - (aeval cst qst a2)
  | <{a1 * a2}> => (aeval cst qst a1) * (aeval cst qst a2)
  | <{a1 / a2}> => (aeval cst qst a1) / (aeval cst qst a2)
  end.

Fixpoint beval {n : nat} (cst : cstate) (qst : qstate n) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval cst qst a1) =? (aeval cst qst a2)
  | <{a1 <= a2}> => (aeval cst qst a1) <=? (aeval cst qst a2)
  | <{~ b1}> => negb (beval cst qst b1)
  | <{b1 && b2}> => andb (beval cst qst b1) (beval cst qst b2)
  end.

Definition pad (n to dim : nat) (U : Unitary (2^n)) : Unitary (2^dim) :=
  if (to + n <=? dim)%nat
  then I (2^to) ⊗ U ⊗ I (2^(dim - n - to))
  else Zero (2^dim) (2^dim).

Definition eval_cnot (dim m n: nat) : Unitary (2^dim) :=
  if (m + 1 =? n) then
    pad 2 m dim CNOT
  else if (n + 1 =? m) then
    pad 2 n dim CNOT
  else
    Zero _ _.

Definition geval (g : gate_exp) : Unitary 2 :=
  match g with
  | GI => I 2
  | GH => H
  | GX => X
  | GZ => Z
  | GY => Y
  end.

Definition qst (n : nat) : qstate n := I n.

Definition U (n : nat) : Unitary n := I n.

Definition krn {n} := kron (qst n) (U n).

Inductive ceval (n : nat) : com -> cstate -> qstate n -> cstate -> qstate n -> Prop :=
  | E_Skip : forall cst qst,
      ceval n <{ skip }> cst qst cst qst
  | E_Ass : forall cst qst a m x,
      aeval cst qst a = m ->
      ceval n <{ x := a }> cst qst (x !-> m; cst) qst
  | E_Init : forall q cst (qst : qstate n),
      ceval n <{ q := 0 }> cst qst cst (kron qst (∣0⟩⟨0∣))
  | E_App : forall cst qst U q,
      ceval n <{ q *= U }> cst qst cst ((geval U) × qst × (geval U) †)
  | E_Seq : forall c1 c2 cst qst cst' qst' cst'' qst'',
      ceval n c1 cst qst cst' qst' ->
      ceval n c2 cst' qst' cst'' qst'' ->
      ceval n <{ c1 ; c2 }> cst qst cst'' qst''
  | E_IfTrue : forall  cst qst cst' qst' b c1 c2,
      beval cst qst b = true ->
      ceval n c1 cst qst cst' qst' ->
      ceval n <{ if b then c1 else c2 end }> cst qst cst' qst'
  | E_IfFalse : forall cst qst cst' qst' b c1 c2,
      beval cst qst b = false ->
      ceval n c2 cst qst cst' qst' ->
      ceval n <{ if b then c1 else c2 end }> cst qst cst' qst'
  | E_WhileFalse : forall cst qst b c,
      beval cst qst b = false ->
      ceval n <{ while b do c end }> cst qst cst qst 
  | E_WhileTrue : forall cst qst cst' qst' cst'' qst'' b c,
      beval cst qst b = true ->
      ceval n c cst qst cst' qst' ->
      ceval n <{ while b do c end }> cst qst cst' qst' ->
      ceval n <{ while b do c end }> cst' qst' cst'' qst''.

