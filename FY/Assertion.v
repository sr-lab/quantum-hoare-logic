From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.ClassicalFacts.
From FY Require Export Utils.
From FY Require Export State.
Import ListNotations.

Definition Assertion (n : nat) : Type := bool_exp * (Unitary n).

Fixpoint Expectation (ns na : nat) 
     (state: list ((total_map nat) * (Unitary ns)))
     (assert: Assertion na) : R :=
    match state with
    | [] => 0%R
    | st :: l => 
        if beval (fst st) (fst assert) then 
        Rplus 
        ( 
          if ns =? na then 
            (fst (trace (Mmult (snd st) (snd assert))))
          else
            (fst (trace (Mmult (kron (snd st) (I (ns - na))) (snd assert))))
        ) 
        (Expectation ns na l assert) 
        else
        (Expectation ns na l assert)
    end
.

Theorem expectation_sum: forall ns na st sts assert,  
  beval (fst st) (fst assert) = true -> 
    (Expectation ns na (st :: sts) assert) = 
    Rplus 
    ( 
        if ns =? na then 
          (fst (trace (Mmult (snd st) 
          (snd assert))))
        else
          (fst (trace (Mmult (kron (snd st) (I (ns - na))) 
          (snd assert))))
    ) 
    (Expectation ns na sts assert) .
Proof.
Admitted.

Definition weaker (ns na1 na2 : nat) 
    (state: list ((total_map nat)*(Unitary ns))) 
    (assert1: Assertion na1) 
    (assert2: Assertion na2) : Prop :=
      (Expectation ns na1 state assert1) 
      <= (Expectation ns na2 state assert2).
(*
Definition Satisfies (n: nat) 
    (state: (total_map nat) * (Unitary (2^n))) (assertion: Assertion n) : bool :=
    beval (fst state) (fst (assertion (fst state))).

Definition X: string := "X".

Definition assert : Assertion 1 := 
  fun (tmn: total_map nat) => pair <{ X <= (3 % nat) }> H.

Definition st : ((total_map nat) * (Unitary 2)) := 
  ((X !-> 1%nat; _ !-> 0%nat), H).

Theorem fstasst: (assert (fst st)) = pair <{ true }> H.
Proof.
    unfold assert.
    simpl.
Qed.

    *)