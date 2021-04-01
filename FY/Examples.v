From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Logic.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
Print fact_in_coq.

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

Example ifexample :
  {{True}}
  if X = 0 then Y := 2 else Y := X + 1 end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'. destruct H. apply eqb_eq' in H0. rewrite H0. lia.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'.
Qed.
