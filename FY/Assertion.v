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

Definition base1 (n: nat) := ( ⟨0∣ ⊗ (I (2 ^(n - 1)))).
Definition base2 (n: nat) := ( ∣0⟩ ⊗ (I (2 ^(n - 1)))).

Definition pre_init (n: nat) (m: Unitary (2^n))
  : Unitary (2^(n - 1%nat)) := (base1 n) × m × (base2 n).

Definition init_sub (n: nat) (P : Assertion n) : Assertion (n - 1) := 
    pair (StateOf P) (pair (PropOf P) (pre_init n (DensityOf P))).

Definition apply_sub n (U: Unitary (2^n)) (P : Assertion n) : Assertion n :=
  pair (StateOf P) (pair (PropOf P) (U† × (DensityOf P) × U)). 

Definition AssertionWithDensity (n m: nat) (P: Assertion n) (U: Unitary (2^m)) : Assertion m := 
  (StateOf P, (PropOf P, U)).

Definition AssertionOf (n: nat) (st: total_map nat) 
(prop: bool_exp) (U: Unitary (2^n)) : Assertion n := 
  (st, (prop, U)).

Definition max (n1: nat) (n2: nat) : nat := if n1 <=? n2 then n2 else n1.

Definition complement (n1 n2: nat) (rho: Unitary (2 ^ n1)) : Unitary (2 ^ (max n1 n2)) := 
  if (n2 <=? n1) then rho else rho ⊗ (I (2 ^ (n2 - n1)))
.

Fixpoint Expectation (ns na : nat) 
     (state: list ((total_map nat) * (Unitary (2 ^ ns))))
     (a: Assertion na) : R :=
    match state with
    | [] => 0%R
    | st :: l => 
        if beval (mergeMaps (fst st) (StateOf a)) (PropOf a) then 
        Rplus 
        ( 
          fst (trace ((complement ns na (snd st)) × (complement na ns (DensityOf a))))
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
          (fst (trace (Mmult (kron (snd st) (I (2^(ns - na)))) 
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
