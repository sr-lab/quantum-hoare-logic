From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.


Definition hoare_triple 
    (np nq: nat)(P : Assertion np) (c : com) (Q : Assertion nq) : Prop :=
    forall ns1 ns2 np nq st1 st2, ceval c st1 st2 -> Cnorm (Expectation ns1 np st1 P) <= Cnorm (Expectation ns2 nq st2 Q).

Theorem equal_expectations: forall ns1 ns2 np nq P st, Cnorm (Expectation ns1 np st P) <= Cnorm (Expectation ns2 nq st P).
Proof.
Admitted.

Theorem fy_skip: forall n P, hoare_triple n n P <{skip}> P.
Proof.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    apply equal_expectations.
Qed.

Definition assign_sub n X a (P : Assertion n) : Assertion n :=
  fun (st : (total_map nat)) => P (X !-> a ; st).

Definition init_sub n (P : Assertion n) : Assertion (n + 1) :=
  fun (st : (total_map nat)) => pair (fst (P st)) (∣0⟩⟨0∣ ⊗ (snd (P st))).

Definition apply_sub n (U: Unitary n) (P : Assertion n) : Assertion n :=
  fun (st : (total_map nat)) => pair (fst (P st)) (Mmult (Mmult U† (snd (P st))) U).

Definition apply_boolean n (b: bool_exp) (P : Assertion n) : Assertion n :=
  fun (st : (total_map nat)) => pair b (snd (P st)).

Theorem fy_sequence: forall np nq nr P Q R c1 c2, 
    hoare_triple np nq P c1 Q ->
    hoare_triple nq nr Q c2 R ->
    hoare_triple np nr P <{ c1;c2 }> R.
Proof.
Admitted.

Theorem fy_assign: forall n x e P, 
    hoare_triple n n (assign_sub n x e P) <{ x :=c e }> P.
Proof.
Admitted.

Theorem fy_init: forall n m P, 
    hoare_triple n n (init_sub n P) <{ q m := 0 }> P.
Proof.
Admitted.

Theorem fy_apply: forall n m G P, 
    hoare_triple n n (apply_sub n (geval G) P) <{ q m *=1 G }> P.
Proof.
Admitted.

(*TODO*)
Theorem fy_measure: forall n x m P, 
    hoare_triple n n P  <{ x :=measQ m }> P.
Proof.
Admitted.

Theorem fy_if: forall (n: nat) (b: bool_exp) (c1 c2: com) P Q, 
    hoare_triple n n (apply_boolean n b P) c1 Q ->
    hoare_triple n n (apply_boolean n <{ ~ b }> P) c2 Q ->
    hoare_triple n n P <{ if b then c1 else c2 end }> Q.
Proof.
Admitted.

Theorem fy_while: forall n b c P,
    hoare_triple n n (apply_boolean n b P) c P ->
    hoare_triple n n P <{ while b do c end }> (apply_boolean n <{ ~ b }> P).
Proof.
Admitted.

Theorem fy_weakness: forall n c st P Q P' Q',
    hoare_triple n n P c Q ->
    weaker n n n st P' P ->
    weaker n n n st Q Q' ->
    hoare_triple n n P' c Q'.
Proof.
Admitted.



 