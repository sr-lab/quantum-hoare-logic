From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.ClassicalFacts.
From FY Require Export Utils.
From FY Require Export State.
Import ListNotations.

Definition Assertion (n: nat) := (total_map nat) -> bool_exp * (Unitary n).

Fixpoint Expectation (ns na : nat) 
     (state: list ((total_map nat) * (Unitary ns))) 
     (assertion: Assertion na) : C :=
    match state with
    | [] => 0%C
    | st :: l => 
        if beval (fst st) (fst (assertion (fst st))) then 
        Cplus 
        (trace (Mmult (kron (snd st) (I (ns - na))) 
        (snd (assertion (fst st))))) 
        (Expectation ns na l assertion)
        else
        (Expectation ns na l assertion)
    end
.

Definition weaker (ns na1 na2 : nat) 
    (state: list ((total_map nat)*(Unitary ns))) 
    (assertion1: Assertion na1) 
    (assertion2: Assertion na2) : Prop :=
    Cnorm (Expectation ns na1 state assertion1) <= Cnorm (Expectation ns na2 state assertion2).
