
From FY2 Require Export Syntax.
From Coq Require Import Strings.String.
From FY2 Require Export Utils.

Definition X : string := "X".

Definition Prog1 : com :=
  <{ q 0 :=q 0;
     q 0 *= GH;
     X :=measQ 0%nat }>.
Print Prog1.

Definition Prog2 : com :=
  <{ q 0 :=q 0;
     q 0 *= GH;
     X :=measQ 0%nat;
     if BEq X 2%nat then
        q 0 *= GZ
    else
        skip
    end }>.
Print Prog2.

