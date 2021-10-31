From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY Require Export Utils.
From FY Require Export Syntax.


Fixpoint aeval (st : total_map nat)
        (a : arith_exp) : nat :=
  match a with
  | ANum m => m
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{a1 / a2}> => (aeval st a1) / (aeval st a2)
  end.

Fixpoint beval (st : total_map nat) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 == a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  | <{b1 || b2}> => orb (beval st b1) (beval st b2)
  end.


Definition geval (g : gate_exp) : Unitary _ :=
  match g with
  | GI => I 2
  | GH => H
  | GX => X
  | GZ => Z
  | GY => Y
  | GCNOT => CNOT
  end.

Definition State (n: nat): Type := list ((total_map nat)*(Unitary (2^n))).

Fixpoint UpdateStateAssign (n : nat) (state: State n) (x: string) (a: arith_exp) :=
  match state with
  | [] => []
  | st :: l => (pair (x !-> (aeval (fst st) a); fst st) (snd st)) :: (UpdateStateAssign n l x a)
  end.

Fixpoint padding (n : nat) (qubit : nat) (U : Unitary 2) : Unitary (2^(n + 1%nat)) :=
  match n with 
  | O%nat => (if qubit =? 0%nat then U else (I 2))
  | S n' => (padding n' qubit U) ⊗ (if qubit =? n then U else I 2)
  end. 

Fixpoint padding4 (n : nat) (qubit : nat) (U : Unitary 4) : Unitary (2^(n + 2%nat)) :=
  match n with 
  | O%nat => (if qubit =? 0%nat then U else (I 2))
  | S n' => (padding4 n' qubit U) ⊗ (if qubit =? n then U else I 2)
  end. 

Fixpoint UpdateStateInit (n : nat) (state: list ((total_map nat)*(Unitary (2^n)))) : list ((total_map nat)*(Unitary (2^(n + 1%nat)))) :=
  match state with
  | [] => []
  | st :: l => if n =? 0%nat then
    (pair (fst st) (∣0⟩⟨0∣)) :: (UpdateStateInit n l)
    else
    (pair (fst st) (∣0⟩ ⊗ (snd st) ⊗ ⟨0∣)) :: (UpdateStateInit n l)
  end.

Fixpoint UpdateStateApply (n : nat) (state: list ((total_map nat)*(Unitary (2^n)))) (qubit : nat) (U: gate_exp): list ((total_map nat)*(Unitary (2^n))) :=
  match state with
  | [] => []
  | st :: l => match U with
      | GCNOT => (pair (fst st) ((padding4 (n - 2%nat) qubit (geval U)) × (snd st) × (padding4 (n - 2%nat) qubit (geval U))†) ) :: (UpdateStateApply n l qubit U)
      | _ => (pair (fst st) ((padding (n - 1%nat) qubit (geval U)) × (snd st) × (padding (n - 1%nat) qubit (geval U))†) ) :: (UpdateStateApply n l qubit U)
    end
  end.

Fixpoint GetMeasurementBasis (nq : nat) (qubit : nat) (isZero : bool) : Unitary (2^(nq + 1%nat)) :=
  match nq with
    | 0%nat => if qubit =? nq then (if isZero then ∣0⟩⟨0∣ else ∣1⟩⟨1∣) else (I 2)
    | S n' => (if qubit =? nq then 
         (if isZero 
           then ((GetMeasurementBasis n' qubit isZero) ⊗ (∣0⟩⟨0∣)) 
          else ((GetMeasurementBasis n' qubit isZero) ⊗ (∣1⟩⟨1∣))) 
          else (GetMeasurementBasis n' qubit isZero) ⊗ (I 2))
  end.

Fixpoint UpdateStateMeasure (n: nat)  (state: list ((total_map nat)*(Unitary (2^n)))) (x : string) (qubit : nat) : list ((total_map nat)*(Unitary (2^n))) :=
  match state with
  | [] => []
  | st :: l => (pair (x !-> 0%nat; fst st) 
     ((GetMeasurementBasis (n - 1%nat) qubit true) × (snd st) × (GetMeasurementBasis (n - 1%nat) qubit true)†)) :: 
     (pair (x !-> 1%nat; fst st) 
     ((GetMeasurementBasis (n - 1%nat) qubit false) × (snd st) × (GetMeasurementBasis (n - 1%nat) qubit false)†)) :: 
     (UpdateStateMeasure n l x qubit)
  end.

Fixpoint Filter (n : nat) (state: list ((total_map nat)*(Unitary (2^n)))) (b : bool_exp): list ((total_map nat)*(Unitary (2^n))) :=
  match state with
  | [] => []
  | st :: l => if (beval (fst st) b) then (st :: (Filter n l b)) else (Filter n l b)
  end.

Fixpoint FilterNeg (n : nat) (state: list ((total_map nat)*(Unitary (2^n)))) (b : bool_exp): list ((total_map nat)*(Unitary (2^n))) :=
  match state with
  | [] => []
  | st :: l => if (negb (beval (fst st) b)) then (st :: (FilterNeg n l b)) else (FilterNeg n l b)
  end.
