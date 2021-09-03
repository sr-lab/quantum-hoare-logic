From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.


Definition hoare_triple 
    (np nq: nat)(P : Assertion np) (c : com) (Q : Assertion nq) : Prop :=
    forall ns1 ns2 np nq st1 st2, ceval c st1 st2 -> Cnorm (Expectation ns1 np st1 P) <= Cnorm (Expectation ns2 nq st2 Q).

Theorem fy_skip: forall n P, hoare_triple n n P <{skip}> P.
Proof.
Admitted.

Theorem fy_sequence: forall np nq nr P Q R c1 c2, 
    hoare_triple np nq P c1 Q ->
    hoare_triple nq nr Q c2 R ->
    hoare_triple np nr P <{ c1;c2 }> R.
Proof.
Admitted.

Definition n : nat := 0%nat.

Check Assertion.

(*
Theorem fy_assign: forall n x e st U, 
    hoare_triple n n ((x !-> e ;st) -> U) <{ x :=c e }> (st -> U).
Proof.
Admitted.
*)



