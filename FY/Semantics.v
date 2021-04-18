From FY Require Export Map.
From FY Require Export Syntax.
From FY Require Export Quantum.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.


Definition state := total_map nat.
Definition empty_st := (_ !-> 0%nat).
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Fixpoint aeval (st : state) (a : arith_exp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{a1 / a2}> => (aeval st a1) / (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
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

Definition geval {n} (dim : nat) (g : gate_exp) : Unitary (2^dim) :=
  match g with
  | GI j => pad n j dim (I 2)
  | GH j => pad n j dim H
  | GX j => pad n j dim X
  | GZ j => pad n j dim Z
  | GY j => pad n j dim Y
  | GCNOT j k => eval_cnot dim j k
  end.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall  st,
      st =[ skip ]=> st
  | E_Ass : forall  st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall  c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall  st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall  st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall  b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall  st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Definition X : string := "X".
