
(* Map *)
From FY Require Export Map.
From FY Require Export Matrix.
From FY Require Export Qubit.

(* State : (classical_map, density_matrix) *)
Definition state {m n : nat} := (total_map R, Matrix m n).












