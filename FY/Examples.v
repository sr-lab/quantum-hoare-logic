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
Definition H : gate_exp := GH (2%nat).
Definition q : string := "q".
Definition zero : nat := 0.
Definition one : nat := 1.
Definition two : nat := 2.
Definition three : nat := 3.
Definition four : nat := 4.


Definition fact_in_coq : com :=
  <{ Z := X;
     Y := one;
     while ~(Z = zero) do
       Y := Y * Z;
       Z := Z - one
     end }>.
Print fact_in_coq.

Example ceval_example1:
  empty_st =[
     X := two;
     if (X <= one)
       then Y := three
       else Z := four
     end
  ]=> (Z !-> four ; X !-> two).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> two).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse. 
Admitted.

Require Import Coq.Arith.PeanoNat.
Check Nat.leb_le.

Example ifexample :
  {{True}}
  if X = zero then Y := two else Y := X + one end
  {{BLe X Y}}.
Proof.
  apply hoare_if.
  Check hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'. destruct H0. apply Nat.eqb_eq in H1. rewrite H1. reflexivity.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'. rewrite Nat.leb_le. lia.
Qed.

Definition BELL : com :=
  <{ q := 0;
     q *= H;
     X :=meas M[ q ] }>.
Print BELL.
