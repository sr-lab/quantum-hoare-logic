From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Inductive derivable: 
    nat -> nat -> 
    Assertion 1 -> com -> Assertion 1 -> Type :=
  | H_Skip : forall n (P: Assertion n),
    derivable n n P <{ skip }> P
  | H_App : forall n G (P: Assertion n) m,
    derivable n n (apply_sub n m (geval G) (is1 G) P) <{ q m *= G }> P
  | H_Init : forall n (P: Assertion n),
    derivable (n - 1)%nat n (init_sub n P) <{ new_qubit }> P
  | H_Asgn : forall n (P: Assertion n) x e,
    derivable n n (AssertPreAsgn P x e) <{ x := e }> P
  | H_Meas_0 : forall n m (P: Assertion n) x,
    derivable n n (AssertPreMeas P x 0 m) <{ x :=meas m }> P
  | H_Meas_1 : forall n m (P: Assertion n) x,
    derivable n n (AssertPreMeas P x 1 m) <{ x :=meas m }> P
  | H_Seq : forall np nq nr (P: Assertion np) c 
                   (Q: Assertion nq) d (R: Assertion nr),
    derivable np nq P c Q -> 
    derivable nq nr Q d R -> 
    derivable np nr P <{ c;d }> R
  | H_If : forall np nq (P: Assertion np) 
                  (Q: Assertion nq) b c1 c2,
    derivable np nq (AssertPreIfTrue P b) c1 Q ->
    derivable np nq (AssertPreIfTrue P (BNot b)) c2 Q ->
    derivable np nq P <{if b then c1 else c2 end}> Q
  | H_While : forall n (P: Assertion n) b c,
    derivable n n (AssertPreIfTrue P b) c P ->
    derivable n n P <{while b do c end}> (AssertPreIfTrue P (BNot b))
  | H_Weakness : forall np nq np' nq' 
         (P: Assertion np) (Q: Assertion nq) 
         (P': Assertion np') (Q': Assertion nq') c,
    derivable np nq P c Q ->
    (forall ns (st: State ns), weaker ns np np' st P' P) ->
    (forall ns (st: State ns), weaker ns nq nq' st Q Q') ->
    derivable np' nq' P' c Q'.

Definition valid {np nq} (P : Assertion np) (c : com) (Q : Assertion nq) 
      : Prop :=
  forall ns1 ns2  (st1: State ns1) (st2: State ns2), 
  (ceval ns1 ns2 c st1 st2) ->
  (Expectation ns1 np st1 P) <= (Expectation ns2 nq st2 Q).

Theorem logic_sound : forall np nq (P: Assertion np) c (Q: Assertion nq),
  derivable np nq P c Q -> valid P c Q.
Proof.
  intros.
  case_eq X.
  - intros. induction X; apply fy_skip.
  - intros. induction X; apply fy_apply.
  - intros. induction X; apply fy_init.
  - intros. induction X; apply fy_assign.  
  - intros. induction X; apply fy_measure.
  - intros. induction X; apply fy_measure.
  - intros. induction X. apply fy_sequence with nq0 Q0.
    induction d0. apply fy_skip. apply fy_apply. 
    apply fy_init. apply fy_assign. apply fy_measure. apply fy_measure.
Admitted.

Theorem logic_complete: forall np nq (P: Assertion np) c (Q: Assertion nq),
  valid P c Q -> derivable np nq P c Q.
Proof.
Admitted.