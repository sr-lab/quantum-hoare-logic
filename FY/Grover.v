From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X : string := "X".
Definition Y0 : string := "Y0".
Definition Y1 : string := "Y1".
Definition Y2 : string := "Y2".
Definition K : string := "K".

Definition U100 : Matrix 8 8 := l2M [[1;0;0;0;0;0;0;0];
                                     [0;1;0;0;0;0;0;0];
                                     [0;0;1;0;0;0;0;0];
                                     [0;0;0;-1%C;0;0;0;0];
                                     [0;0;0;0;1;0;0;0];
                                     [0;0;0;0;0;1;0;0];
                                     [0;0;0;0;0;0;1;0];
                                     [0;0;0;0;0;0;0;1]].

Lemma U100W: U100 × ∣1,0,0⟩ = -1 * ∣1,0,0⟩.
Proof.
Admitted.

(*TODO: not complete*)
Lemma U100NW: forall (w: Vector 8), w <> ∣1,0,0⟩ -> U100 × w = w.
Proof.
Admitted.

Definition G := GOracle 8 U100.

Lemma kron_I_1: kron (I 2) (I 1) = I 2.
Proof.
Admitted.

Definition GROVER : com :=
  <{
    q 0 := 0;
    q 1 := 0;
    q 2 := 0;
    q 0 *=1 GH;
    q 1 *=1 GH;
    q 2 *=1 GH;
    K :=c (3 % nat); (* 3 ~ sqrt(8) *)
    X :=c (0 % nat);
    while X <= K do
      q 0 1 2 *=3 G;
      X :=c (X + 1%nat)
    end;
    Y0 :=measQ 0;
    Y1 :=measQ 1;
    Y2 :=measQ 2
  }>.

Print GROVER.

Theorem final_state: ceval GROVER [(( _ !-> 0%nat), I 1)] [(( X !-> 3%nat ; K !-> 3%nat ; Y0 !-> 0%nat ; Y1 !-> 0%nat ;Y2 !-> 1%nat; _ !-> 0%nat), ∣0⟩⟨0∣ )] .
Proof.
  eapply E_Seq.
  apply E_Init.
Admitted.




