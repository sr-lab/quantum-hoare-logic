Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From FY Require Import Utils.

Inductive arith_exp : Type :=
  | AId (x : string)
  | ANum (n : nat)
  | APlus (a1 a2 : arith_exp)
  | AMinus (a1 a2 : arith_exp)
  | AMult (a1 a2 : arith_exp)
  | ADiv (a1 a2 : arith_exp).

Inductive bool_exp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : arith_exp)
  | BLe (a1 a2 : arith_exp)
  | BNot (b : bool_exp)
  | BAnd (b1 b2 : bool_exp)
  | BOr (b1 b2 : bool_exp).

Inductive gate_exp : Type :=
  | GH
  | GX 
  | GY 
  | GZ
  | GI
  | GCNOT.

Coercion AId : string >-> arith_exp.
Coercion ANum : nat >-> arith_exp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x % nat" := (x%nat) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "x / y" := (ADiv x y) (in custom com at level 40, left associativity).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x == y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y" := (BOr x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : arith_exp)
  | CMeas (x : string) (q : nat)
  | CInit
  | CAppOne (q : nat) (U : gate_exp)
  | CAppTwo (q1 : nat) (q2 : nat) (U : gate_exp)
  | CSeq (c1 c2 : com)
  | CIf (b : bool_exp) (c1 c2 : com)
  | CWhile (b : bool_exp) (c : com).

Notation "'skip'" :=
    CSkip (in custom com at level 0) : com_scope.
Notation "x ':=' y" :=
    (CAss x y)
       (in custom com at level 0, x constr at level 0,
        y at level 40, no associativity) : com_scope.
Notation "x ':=meas' n" :=
    (CMeas x n)
       (in custom com at level 0, x constr at level 0,
        n constr at level 77, no associativity) : com_scope.
Notation "'new_qubit'" :=
    (CInit)
       (in custom com at level 0, no associativity) : com_scope.
Notation "'q' n *= U" :=
    (CAppOne n U)
       (in custom com at level 0, n constr at level 0, 
       U at level 85, no associativity) : com_scope.
Notation "'q' n m *= U" :=
    (CAppTwo n m U)
       (in custom com at level 0, n constr at level 0, 
        m constr at level 0, U at level 85,
        no associativity) : com_scope.
Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
       y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
       (in custom com at level 89, x at level 99, y at level 99) : com_scope.
