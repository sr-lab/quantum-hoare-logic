From FY Require Import Semantics.
From FY Require Import Map.
From Coq Require Import Lia.
From Coq Require Import Strings.String.

Definition X : string := "X".
Definition Y : string := "Y".

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : arith_exp) : Aexp := fun st => aeval st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : arith_exp >-> Aexp.
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Definition hoare_triple
  (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  unfold assn_sub in H0.
  assumption.
Qed.


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. 
  inversion H; subst. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

Ltac assn_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example hoare_asgn_example3 : forall (a:arith_exp) (n:nat),
  {{a = n}}
  X := a; skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bool_exp >-> Assertion.

Arguments bassn /.
Hint Unfold bassn : core.

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b : bool_exp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

Lemma eqb_eq': forall (n m: nat), Nat.eqb n m = true <-> n = m.
Proof.
Admitted.


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