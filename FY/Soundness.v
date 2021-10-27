From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Inductive derivable (np nq: nat) : Assertion np -> com -> Assertion nq -> Type :=
| H_Skip : forall P,
    derivable P <{skip}> P
| H_Asgn : forall Q V a,
    derivable (Q [V ⊢> a]) <{X := a}> Q
| H_Seq : forall P c Q d R,
    derivable P c Q -> derivable Q d R -> derivable P <{c;d}> R
| H_If : forall P Q b c1 c2,
  derivable (fun st => P st ∧ bassn b st) c1 Q ->
  derivable (fun st => P st ∧ ~(bassn b st)) c2 Q ->
  derivable P <{if b then c1 else c2 end}> Q
| H_While : forall P b c,
  derivable (fun st => P st ∧ bassn b st) c P ->
  derivable P <{while b do c end}> (fun st => P st ∧ ~ (bassn b st))
| H_Consequence : forall (P Q P' Q' : Assertion) c,
  derivable P' c Q' ->
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  derivable P c Q.

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Theorem logic_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
Admitted.

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
Admitted.