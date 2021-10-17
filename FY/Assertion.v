From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Logic.ClassicalFacts.
From FY Require Export Utils.
From FY Require Export State.
Import ListNotations.

Definition Assertion (n: nat) : Type := 
  (total_map nat) * (bool_exp * (Unitary (2^n))).

Definition StateOf {n: nat} (a: Assertion n) : total_map nat := fst a.

Definition PropOf {n: nat} (a: Assertion n): bool_exp := fst (snd a).

Definition DensityOf {n: nat} (a: Assertion n) := snd ( snd a).

Definition init_sub (n: nat) (P : Assertion n) : Assertion (n - 1) := 
    pair (StateOf P) (pair (PropOf P) (( ⟨0∣ ⊗ (I (2 ^(n - 1)))) × (DensityOf P) × (∣0⟩ ⊗ (I (2 ^(n - 1)))))).

Definition apply_sub n (U: Unitary n) (P : Assertion n) : Assertion n :=
  pair (StateOf P) (pair (PropOf P) (U† × (DensityOf P) × U)). 

Fixpoint Expectation (ns na : nat) 
     (state: list ((total_map nat) * (Unitary (2 ^ns))))
     (a: Assertion na) : R :=
    match state with
    | [] => 0%R
    | st :: l => 
        if beval (mergeMaps (StateOf a) (fst st)) (PropOf a) then 
        Rplus 
        ( 
          if ns =? na then 
            (fst (trace ( (snd st) × (DensityOf a) )))
          else
            (fst (trace (((snd st) ⊗ (I (ns - na))) × (DensityOf a))))
        ) 
        (Expectation ns na l a) 
        else
        (Expectation ns na l a)
    end
.

Theorem expectation_sum_true: forall ns na (st: (total_map nat)*(Unitary (2 ^ ns))) (sts: list ((total_map nat)*(Unitary (2 ^ns)))) assert,  
  beval (mergeMaps (StateOf assert) (fst st)) (PropOf assert) = true -> 
    (Expectation ns na (st :: sts) assert) = 
    Rplus 
    ( 
        if ns =? na then 
          (fst (trace (Mmult (snd st) 
          (DensityOf assert))))
        else
          (fst (trace (Mmult (kron (snd st) (I (ns - na))) 
          (DensityOf assert))))
    ) 
    (Expectation ns na sts assert) .
Proof.
Admitted.

Theorem expectation_sum_false: forall ns na st sts assert,  
  beval (mergeMaps (StateOf assert) (fst st)) (PropOf assert) = false -> 
    (Expectation ns na (st :: sts) assert) = 
    (Expectation ns na sts assert) .
Proof.
Admitted.


Definition weaker (ns na1 na2 : nat) 
    (state: list ((total_map nat)*(Unitary (2 ^ns)))) 
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