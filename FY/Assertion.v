From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
Import ListNotations.

Definition Assertion (n: nat) := pair Prop (Unitary n).

(*  *)
Fixpoint Expectation (ns na : nat) 
     (state: list ((total_map nat) * (Unitary ns))) 
     (assertion: Assertion na) : C :=
    match state with
    | [] => 0%C
    | st :: l => 
        match (fst (assertion (fst st))) with
         | True => Cplus 
                    (trace (Mmult (kron (snd st) (I (ns - na))) 
                    (snd (assertion (fst st))))) 
                    (Expectation ns na l assertion)
        end
    end
.






Definition weaker (ns na1 na2 : nat) (state: list ((total_map nat)*(Unitary ns))) (assertion1: Assertion na1) (assertion2: Assertion na2) : Prop :=
    Cnorm (Expectation ns na1 state assertion1) <= Cnorm (Expectation ns na2 state assertion2).

