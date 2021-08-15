
From FY2 Require Export Syntax.
From FY2 Require Export Utils.
From Coq Require Import Strings.String.

Definition q : string := "q".
Definition H : gate_exp := GH.
Definition Z : gate_exp := GZ.
Definition X : string := "X".

Definition Prog1 : com :=
  <{ q :=q 0;
     q *= H;
     X :=meas q }>.
Print Prog1.

Definition Prog2 : com :=
  <{ q :=q 0;
     q *= H;
     X :=meas q;
     if BEq X 2%nat then
        q *= Z
    else
        skip
    end }>.
Print Prog2.



