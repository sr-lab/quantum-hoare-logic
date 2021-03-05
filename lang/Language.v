
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

(* Syntax *)
(*  
  skip
  | x := e
  | x :=$ g
  | x := measure M[q]
  | q := 0
  | q:=U.q
  | S0 ; S1
  | if b then S1 else S0 end
  | while b do S end
*)

Declare Custom Entry com.
Declare Scope com_scope.

Inductive arith_exp : Type :=
  | Num (n : nat)
  | Id (x : string)
  | Plus (a1 a2 : arith_exp)
  | Minus (a1 a2 : arith_exp)
  | Mult (a1 a2 : arith_exp).

Inductive bool_exp : Type :=
  | BTrue
  | BFalse
  | Eq (b1 b2 : arith_exp)
  | Le (b1 b2 : arith_exp)
  | Not (b : bool_exp)
  | And (b1 b2 : bool_exp).

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : arith_exp -> nat -> Prop :=
  | E_Num (n : nat) :
      (Num n) ==> n
  | E_Plus (e1 e2 : arith_exp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (Plus e1 e2) ==> (n1 + n2)
  | E_Minus (e1 e2 : arith_exp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (Minus e1 e2) ==> (n1 - n2)
  | E_Mult (e1 e2 : arith_exp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (Mult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Reserved Notation "e '==>b' b" (at level 90, left associativity).

Inductive bevalR: bool_exp -> bool -> Prop :=
  | E_True :
  bevalR BTrue true
  | E_False:
  bevalR BFalse false
  | E_Eq (e1 e2 : arith_exp) (n1 n2 : nat) :
    (e1 ==> n1) -> (e2 ==> n2) -> (Eq e1 e2) ==>b (n1 =? n2)
  | E_Le (e1 e2 : arith_exp) (n1 n2 : nat) :
    (e1 ==> n1) -> (e2 ==> n2) -> (Le e1 e2) ==>b (n1 <=? n2)
  | E_Not (e : bool_exp) (b : bool) :
    e ==>b b -> (Not e) ==>b (negb b)
  | E_And (e1 e2 : bool_exp) (b1 b2 : bool) :
    (e1 ==>b b1) -> (e2 ==>b b2) -> (And e1 e2) ==>b (andb b1 b2)
where "e '==>b' b" := (bevalR e b) : type_scope.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition state := total_map nat.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion Id : string >-> arith_exp.
Coercion Num : nat >-> arith_exp.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (Plus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (Minus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (Mult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (Le x y) (in custom com at level 70, no associativity).
Notation "x = y" := (Eq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (And x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (Not b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Definition example_aexp : arith_exp := <{ 3 + (X * 2) }>.
Definition example_bexp : bool_exp := <{ true && ~(X <= 4) }>.

Fixpoint arith_eval (st : state) (a : arith_exp) : nat :=
  match a with
  | Num n => n
  | Id x => st x
  | <{a1 + a2}> => (arith_eval st a1) + (arith_eval st a2)
  | <{a1 - a2}> => (arith_eval st a1) - (arith_eval st a2)
  | <{a1 * a2}> => (arith_eval st a1) * (arith_eval st a2)
  end.
Fixpoint bool_eval (st : state) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (arith_eval st a1) =? (arith_eval st a2)
  | <{a1 <= a2}> => (arith_eval st a1) <=? (arith_eval st a2)
  | <{~ b1}> => negb (bool_eval st b1)
  | <{b1 && b2}> => andb (bool_eval st b1) (bool_eval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Inductive command : Type :=
  | Skip
  | Ass (x : string) (a : arith_exp)
  | Seq (c1 c2 : command)
  | AssDist (x : string) (g : arith_exp -> arith_exp)
  | If (b : bool_exp) (c1 c2 : command)
  | While (b : bool_exp) (c : command).

Open Scope com_scope.

Notation "'skip'"  :=
    Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
    (Ass x y)
       (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x :=$ g"  :=
    (AssDist x g)
       (in custom com at level 0, x constr at level 0,
        g at level 86, no associativity) : com_scope.
Notation "x ; y" :=
    (Seq x y)
      (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
    (If x y z)
      (in custom com at level 89, x at level 99,
       y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
    (While x y)
       (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation "st '=[' c ']=>' st'"
       (at level 40, c custom com at level 99,
        st constr, st' constr at next level).

Inductive ceval : command -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass : forall st a n x,
    arith_eval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      bool_eval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
    bool_eval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
    bool_eval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
    bool_eval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  -apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.  
Qed.

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
Definition Aexp_of_aexp (a : arith_exp) : Aexp := fun st => arith_eval st a.
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
  (P : Assertion) (c : command) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> arith_eval st a ; st).

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

























