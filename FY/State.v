From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From FY2 Require Export Utils.
From FY2 Require Export Syntax.

Fixpoint aeval (st : total_map nat)
        (a : arith_exp) : nat :=
  match a with
  | ANum m => m
  | ACId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{a1 / a2}> => (aeval st a1) / (aeval st a2)
  end.

Fixpoint beval (st : total_map nat) (b : bool_exp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
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

Definition quantum_registry := string -> nat.

Fixpoint ApplyOneQubitGate (n : nat) (qubit : nat) (U : Unitary 2) : Unitary n :=
  match n with 
  | O%nat => if qubit =? 0%nat then U else I 2
  | S n' => (if qubit =? n' then U else I 2) ⊗ (ApplyOneQubitGate n' qubit U)
  end. 

Fixpoint ApplyTwoQubitsGate (n : nat) (qubit : nat) (U : Unitary 4) : Unitary n :=
  match n with
  | 0%nat => if qubit =? 0%nat then U else I 4
  | S n' => if qubit =? n' then (U ⊗ (ApplyTwoQubitsGate (n' - 1) qubit U)) else ((I 2) ⊗ (ApplyTwoQubitsGate n' qubit U))
  end.

Fixpoint UpdateStateAssign (n : nat) (state: list ((total_map nat)*(Unitary n))) (x : string) (a : arith_exp) : list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => (pair (x !-> (aeval (fst st) a); fst st) (snd st)) :: (UpdateStateAssign n l x a)
  end.

Fixpoint UpdateStateInit (n : nat) (state: list ((total_map nat)*(Unitary n))) (qubit : nat): list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => (pair (fst st) (∣0⟩⟨0∣ ⊗ (snd st))) :: (UpdateStateInit n l qubit)
  end.

Fixpoint UpdateStateApply (n : nat) (state: list ((total_map nat)*(Unitary n))) (qubit : nat) (U: gate_exp): list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => match U with
      | GCNOT => (pair (fst st) ((ApplyTwoQubitsGate n qubit (geval U)) ⊗ (snd st) ⊗ (ApplyTwoQubitsGate n qubit (geval U))†) ) :: (UpdateStateApply n l qubit U)
      | _ => (pair (fst st) ((ApplyOneQubitGate n qubit (geval U)) ⊗ (snd st) ⊗ (ApplyOneQubitGate n qubit (geval U))†) ) :: (UpdateStateApply n l qubit U)
    end
  end.

Fixpoint UpdateStateMeasure (n : nat)  (state: list ((total_map nat)*(Unitary n))) (x : string) (qubit : nat) : list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => (pair (x !-> 0%nat; fst st) (∣0⟩⟨0∣ ⊗ (snd st))) :: (pair (x !-> 1%nat; fst st) (∣1⟩⟨1∣ ⊗ (snd st))) :: (UpdateStateMeasure n l x qubit)
  end.

Fixpoint Filter (n : nat) (state: list ((total_map nat)*(Unitary n))) (b : bool_exp): list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => if (beval (fst st) b) then (st :: (Filter n l b)) else (Filter n l b)
  end.

Fixpoint FilterNeg (n : nat) (state: list ((total_map nat)*(Unitary n))) (b : bool_exp): list ((total_map nat)*(Unitary n)) :=
  match state with
  | [] => []
  | st :: l => if (negb (beval (fst st) b)) then (st :: (FilterNeg n l b)) else (FilterNeg n l b)
  end.
