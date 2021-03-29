Require Export Coq.Strings.String.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
  (x : string) (v : A) := fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).