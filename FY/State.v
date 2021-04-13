
(* Map *)
From FY Require Export Map.
From FY Require Export Matrix.
From FY Require Export Quantum.

(* State : (classical_map, density_matrix) *)

Definition cstate : Type := total_map nat.
Definition qstate (n : nat) : Type := Matrix n n.

Definition state (n : nat) := cstate -> (qstate n).



(* empty state *)
(* update state - classical variable *)
(* update state - quantum variable *)


