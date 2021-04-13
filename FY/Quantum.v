Require Import FunctionalExtensionality.
Require Import Bool.
Require Import List.
Import ListNotations.
From FY Require Export Matrix.

(* Definitions *)

Notation Qubit := (Vector 2).

Definition qubit0 : Qubit := l2V [1;0].

Definition qubit1 : Qubit := l2V [0;1].

Notation "∣ 0 ⟩" := qubit0.
Notation "∣ 1 ⟩" := qubit1.
Notation "⟨0∣" := qubit0†.
Notation "⟨1∣" := qubit1†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).
Arguments qubit0 _ _ /.
Arguments qubit1 _ _ /.

Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then ⟨0∣ else ⟨1∣.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ∣0⟩ else ∣1⟩.

Notation "'∣' x '⟩'" := (ket x).
Notation "'⟨' x '∣'" := (bra x).

Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).

Transparent bra.
Transparent ket.
Transparent qubit0.
Transparent qubit1.

Definition WF_Qubit (ϕ : Qubit) : Prop := (⎸(ϕ 0 0)%nat⎸² + ⎸(ϕ 1 0)%nat⎸² = 1)%C.

Notation Unitary n := (Matrix n n).

Definition WF_Unitary {n} (U : Unitary n) := U † × U == I n.

Definition X : Unitary 2 := l2M [[0;1];
                                 [1;0]].

Definition Y : Unitary 2 := l2M [[0; -i];
                                 [i; 0]].

Definition Z : Unitary 2 := l2M [[1; 0];
                                 [0; -(1)]].

Definition H : Unitary 2 := l2M [[/√2; /√2];
                                 [/√2;-/√2]].

Definition CNOT : Unitary 4 := l2M [[1;0;0;0];
                                    [0;1;0;0];
                                    [0;0;0;1];
                                    [0;0;1;0]].
                                  
Definition NOTC : Unitary 4 := l2M [[1; 0; 0; 0];
                                    [0; 0; 0; 1];
                                    [0; 0; 1; 0];
                                    [0; 1; 0; 0]].

Definition q_plus : Qubit := l2V [/√2; /√2].
Definition q_minus : Qubit := l2V [/√2; -/√2].
Arguments q_plus _ _ /.
Arguments q_minus _ _ /.
Notation "∣ + ⟩" := q_plus.
Notation "∣ - ⟩" := q_minus.

Inductive measure : Qubit -> (R * Qubit) -> Prop :=
  | measure0 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 0%nat 0%nat ⎸², ∣0⟩)
  | measure1 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 1%nat 0%nat ⎸², ∣1⟩).

Notation QState n := (Vector (2^n)).

Notation Density n := (Matrix n n) (only parsing).

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
  WF_Matrix φ /\ φ† × φ = I  1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ, Pure_State_Vector φ /\ ρ = φ × φ†.

Inductive Mixed_State {n} : Matrix n n -> Prop :=
  | Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
  | Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                       Mixed_State (p * ρ1 + (1-p)%R * ρ2).

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix ρ.
Proof. Admitted. 

Hint Resolve WF_Pure : wf_db.

Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix ρ.
Proof. Admitted. 

Hint Resolve WF_Mixed : wf_db.

Lemma pure0 : Pure_State ∣0⟩⟨0∣. 
Proof. exists ∣0⟩. intuition. split. auto with wf_db. Abort.
(* Properties *)

Lemma qubit_decomposition : forall (ϕ : Qubit), exists (α β : C), ϕ == α * ∣0⟩ + β * ∣1⟩.
Proof.
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat.
  lma.
Qed.

Theorem WF_Qubit_alt : forall ϕ : Qubit, WF_Qubit ϕ <-> ϕ† × ϕ == I 1.
Proof.
  intros.
  split.
  - intros. unfold WF_Qubit in H0. unfold adjoint, Mmult. 
Admitted.

Lemma WF_qubit0 : WF_Qubit ∣0⟩. Proof. lca. Qed.
Lemma WF_qubit1 : WF_Qubit ∣1⟩. Proof. lca. Qed.

Lemma valid_qubit_function : exists(P : Matrix 2 2 -> Prop),
  forall (A : Matrix 2 2) (ϕ : Qubit),
  P A -> WF_Qubit ϕ -> WF_Qubit (A × ϕ).
Proof.
  eexists.
  intros A ϕ p Q.
  rewrite WF_Qubit_alt.
  rewrite WF_Qubit_alt in Q.
  unfold inner_product.
  rewrite Mmult_adjoint.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc (A†)).
  assert (P: A† × A = I 2). apply p.
  rewrite P.
  rewrite Mmult_1_l.
  apply Q.
Qed.

Lemma WF_X : WF_Unitary X. Proof. lma. Qed.

Lemma X0 : X × ∣0⟩ == ∣1⟩. Proof. lma. Qed.

Lemma X1 : X × ∣1⟩ == ∣0⟩. Proof. lma. Qed.

Lemma WF_Y : WF_Unitary Y. Proof. lma. Qed.

Lemma Y0 : Y × ∣0⟩ == i * ∣1⟩. Proof. lma. Qed.

Lemma Y1 : Y × ∣1⟩ == -i * ∣0⟩. Proof. lma. Qed.

Lemma WF_Z : WF_Unitary Z. Proof. lma. Qed.

Lemma Z0 : Z × ∣0⟩ == ∣0⟩. Proof. lma. Qed.

Lemma Z1 : Z × ∣1⟩ == -(1) * ∣1⟩. Proof. lma. Qed.

Lemma WF_H : WF_Unitary H.
Proof.
  unfold WF_Unitary, H; autounfold with U_db; simpl.
  by_cell; try lca.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
Qed.

Lemma H0 : H × ∣0⟩ == ∣+⟩. Proof. lma. Qed.
Lemma H1 : H × ∣1⟩ == ∣-⟩. Proof. lma. Qed.

Lemma Hplus : H × ∣+⟩ == ∣0⟩.
Proof.
  unfold H, Mmult, q_plus; simpl.
  by_cell; simpl; try lca.
  C_field_simplify.
  lca.
Qed.

Lemma Hminus : H × ∣-⟩ == ∣ 1 ⟩.
Proof.
  unfold H, Mmult, q_minus; simpl.
  by_cell; C_field_simplify; lca.
Qed.

Theorem Htwice : forall ϕ : Qubit, H × (H × ϕ) == ϕ.
Proof.
  unfold H, Mmult; simpl. by_cell; C_field_simplify. lca. lca.
Qed.

Lemma measure0_idem : forall ϕ p, measure ∣0⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣0⟩.
Proof.
  intros ϕ p M NZ.
  inversion M; subst.
  - reflexivity.
  - contradict NZ. lra.
Qed.

Lemma measure1_idem : forall ϕ p, measure ∣1⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣1⟩.
Proof.
  intros ϕ p M NZ.
  inversion M; subst.
  - contradict NZ. lra.
  - reflexivity.
Qed.

Lemma measure_plus : forall ϕ p, measure ∣+⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros ϕ p M.
  inversion M; subst.
  - R_field.
  - R_field.
Qed.

Lemma measure_minus : forall ϕ p, measure ∣-⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros ϕ p M.
  inversion M; subst.
  - R_field.
  - R_field.
Qed.

Hint Unfold H X Y Z qubit0 qubit1 q_plus q_minus : U_db.
    
Lemma CNOT00 : CNOT × ∣0,0⟩ == ∣0,0⟩. Proof. lma. Qed.
Lemma CNOT01 : CNOT × ∣0,1⟩ == ∣0,1⟩. Proof. lma. Qed.
Lemma CNOT10 : CNOT × ∣1,0⟩ == ∣1,1⟩. Proof. lma. Qed.
Lemma CNOT11 : CNOT × ∣1,1⟩ == ∣1,0⟩. Proof. lma. Qed.



