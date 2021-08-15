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

(* --- Real Numbers *)

Require Reals. 
Require Psatz.
Require Ring.
Require Field.

Module FYR.

Parameter R : Set.
Delimit Scope R_scope with R.
Local Open Scope R_scope.

Parameter R0 : R.
Parameter R1 : R.

Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

Fixpoint INR (n : nat) : R :=
  match n with
  | O => R0
  | 1 => R1
  | S n' => R1 + INR n'
  end.

Coercion INR : nat >-> R.

Check 3 * 5.

Axiom R1_neq_R0 : INR 1 <> INR 0.
Axiom Rplus_comm : forall r1 r2 : R, r1 + r2 = r2 + r1.
Axiom Rplus_assoc : forall r1 r2 r3 : R, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Rplus_opp_r : forall r : R, r + - r = 0.
Axiom Rplus_0_l : forall r : R, 0 + r = r.


Lemma Rplus_0_r : forall r : R, r + 0 = r.
Proof.
  intros r.
  rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.

Lemma Rplus_opp_l : forall r, -r + r = 0.
Proof.
  intros r.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : -0 = 0.
Proof.
  rewrite <- (Rplus_0_l (-0)).
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma R0_unique : forall r1 r2, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros.
  rewrite <- Rplus_0_r in H.
  eapply Rplus_cancel_l.
  apply H.
Qed.

Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Axiom Rmult_1_l : forall r:R, 1 * r = r.
Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intros r.
  apply (R0_unique (r * 0)).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3:R, 
(r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros r1 r2 r3.
  rewrite Rmult_comm.
  rewrite Rmult_plus_distr_l.
  rewrite 2 (Rmult_comm r3).
  reflexivity.
  
  Qed.

Lemma Rinv_r : forall r:R, r <> 0 -> r * / r = 1.
Proof.
  intros. rewrite Rmult_comm.
  apply Rinv_l.
  assumption.
Qed.

Export Ring.
Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  (* addition *)
  (* left identity *) apply Rplus_0_l.
  (* commutativity *) apply Rplus_comm.
  (* associativity *) intros; rewrite Rplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Rmult_1_l.
  (* commutativity *) apply Rmult_comm.
  (* associativity *) intros; rewrite Rmult_assoc; easy.
  (* distributivity *) apply Rmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Rplus_opp_r.
Defined.

Add Ring RRing : R_Ring_Theory.

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  (* ring axioms *) apply R_Ring_Theory.
  (* 0 <> 1 *) apply R1_neq_R0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Rinv_l.
Defined.
Add Field RField : R_Field_Theory.

Example ring_test1 : forall(x : R), x + x = 2 * x. 
Proof. 
  intros. simpl. ring. 
Qed.

Example ring_test2 : forall(x y z: R), 
  x * y + z = z + y * x. 
Proof. 
  intros. ring. 
Qed.

Example field_test1 : forall(x y : R), x <> 0 -> x * y / x = y.
Proof. 
  intros. 
  field. 
  assumption. 
Qed.

Parameter Rlt : R -> R -> Prop.
Infix "<" := Rlt : R_scope.
Definition Rgt (r1 r2:R) : Prop := r2 < r1.
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.
Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.
Axiom total_order_T : forall r1 r2 : R, {r1 < r2} + {r1 = r2} + {r1 > r2}.
Axiom Rlt_asym : forall r1 r2 : R, r1 < r2 -> ~r2 < r1.
Axiom Rlt_trans : forall r1 r2 r3 : R, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Rplus_lt_compat_l : forall r r1 r2 : R, r1 < r2 -> r + r1 < r + r2.
Axiom Rmult_lt_compat_l : forall r r1 r2 : R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

Definition is_upper_bound (E:R -> Prop) (m:R) := 
  forall x:R, E x -> x <= m.

Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.

Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

Axiom completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.

Lemma Rlt_0_1 : 0 < 1. Admitted.

Definition lt_sqrt2 (x : R) := x * x < 2.

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - rewrite <- (Rplus_0_r x).
    eapply Rlt_trans.
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
    rewrite Rplus_comm.
    apply Rplus_lt_compat_l.
    assumption.
  - rewrite E.
    rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
  - assert (x * 1 < x * x).
    apply Rmult_lt_compat_l.
    eapply Rlt_trans.
    apply Rlt_0_1.
    apply G.
    apply G.
    rewrite Rmult_comm, Rmult_1_l in H0.
    eapply Rlt_trans.
    apply H0.
    apply H.
Qed.

End FYR.

Export Reals.
Export Psatz.
Open Scope R_scope.

Definition lt_sqrt2 (x : R) := x * x < 2.
Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  destruct (total_order_T x 1) as [[L | E] | G]; try lra.
  assert (x * 1 <= x * x).
  { apply Rmult_le_compat_l; lra. }
  lra.
Qed.

Notation "√ x" := (sqrt x) (at level 0).

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros. simpl. rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat),
  0 <= x -> √ x ^ (S (S n)) = (x * √ x ^ n)%R.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> (√ r)%R <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof.
  apply sqrt_inv; lra.
Qed.


(* --- Complex Numbers *)
Delimit Scope C_scope with C.
Bind Scope C_scope with C.
Open Scope C_scope.

Definition C : Type := R * R.
Definition RtoC (r : R) : C := (r,0).
Coercion RtoC : R >-> C.

Notation i := (0,1).
Notation "0" := (RtoC 0) : C_scope.
Notation "1" := (RtoC 1) : C_scope.

Definition Cplus (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).

Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cminus (c1 c2 : C) : C := Cplus c1 (Copp c2).

Definition Cmult (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

Definition Cinv (c : C) : C :=
    (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).

Definition Cdiv (c1 c2 : C) : C := Cmult c1 (Cinv c2).

Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Definition Cnorm (c : C) : R := √ (Cnorm2 c).
Arguments Cnorm2 c /.
Arguments Cnorm c /.
Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.
Notation "⎸ x ⎸²" := (Cnorm2 x) : C_scope.

Lemma c_proj_eq : forall (c1 c2 : C),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. 
  intros. 
  destruct c1, c2. 
  simpl in *. 
  subst. 
  reflexivity. 
Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

Open Scope C_scope.

Lemma C1_neq_C0 : 1 <> 0. 
Proof. 
  intros F. 
  inversion F. 
  lra. 
Qed.

Lemma Cplus_comm : forall c1 c2 : C, c1 + c2 = c2 + c1. 
Proof. 
  intros. lca. 
Qed.

Lemma Cplus_assoc : forall c1 c2 c3 : C, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall c : C, c + - c = 0. Proof. intros. lca. Qed.

Lemma Cplus_0_l : forall c : C, 0 + c = c. Proof. intros. lca. Qed.

Lemma Cmult_comm : forall c1 c2:C, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.

Lemma Cmult_assoc : forall c1 c2 c3:C, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.

Lemma Cmult_1_l : forall c:C, 1 * c = c. Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_r : forall c1 c2 c3:C, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.

Lemma Cinv_l : forall c:C, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.

Lemma C_Field_Theory : @field_theory C 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.
Add Field CField : C_Field_Theory.

Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : C, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:C, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:C, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:C, c * 1 = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_l : forall c1 c2 c3:C, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_r : forall c:C, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.
Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.
Lemma RtoC_neq : forall (r1 r2 : R), r1 <> r2 -> RtoC r1 <> RtoC r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).
Notation "a ^*" := (Cconj a) (at level 10) : C_scope.
Lemma Cconj_R : forall r : R, r^* = r. Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0. Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2. Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.

Lemma Conj_mult_norm2 : forall c, c^* * c = ⎸c⎸².
Proof.
  intros.
  lca.
Qed.

Fixpoint Csum (f : nat -> C) (n : nat) : C :=
  match n with
  | O => 0
  | S n' => Csum f n' + f n'
  end.

Lemma Csum_0 : forall (f : nat -> C) (n : nat),
  (forall x, (x < n)%nat -> f x = 0) ->
  Csum f n = 0.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite H by lia.
    rewrite IHn. lca.
    intros. apply H; lia.
Qed.

Lemma Csum_eq : forall (f g : nat -> C) (n : nat),
  (forall x, (x < n)%nat -> f x = g x) ->
  Csum f n = Csum g n.
Proof.
  intros f g n H.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Csum_plus : forall (f g : nat -> C) (n : nat),
    Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
  intros f g n.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma Csum_mult_l : forall (c : C) (f : nat ->  C) (n : nat),
    c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  - simpl. lca.
  - simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_mult_r : forall (c : C) (f : nat ->  C) (n : nat),
    Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  - simpl; lca.
  - simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_unique : forall (f : nat -> C) (k : C) (n x : nat),
  (x < n)%nat ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof.
  intros.
Admitted.

Lemma Csqrt_inv : forall (r : R), 0 < r -> RtoC (√ (/ r)) = (/ √ r).
Proof.
  intros r H.
  apply c_proj_eq; simpl.
  field_simplify_eq [(pow2_sqrt r (or_introl H)) (sqrt_inv r H)].
  rewrite Rinv_r. reflexivity.
  apply sqrt_neq_0_compat; lra.
  apply sqrt_neq_0_compat; lra.
  field. apply sqrt_neq_0_compat; lra.
Qed.

Ltac nonzero :=
  repeat match goal with
  | |- _ /\ _ => split
  end;
  try match goal with
  | |- (?x <> 0)%C => apply RtoC_neq
  end;
  repeat match goal with
  | |- (√?x <> 0)%R => apply sqrt_neq_0_compat
  | |- (/?x <> 0)%R => apply Rinv_neq_0_compat
  end;
  match goal with
  | |- (_ <> _)%R => lra
  | |- (_ < _)%R => lra
  end.

Lemma Csqrt2_inv : RtoC (√ (/ 2)) = (/ √ 2).
Proof. apply Csqrt_inv. lra. Qed.

Lemma Csqrt2_square : √2 * √2 = 2.
  Proof.
    eapply c_proj_eq; simpl; try lra.
    rewrite Rmult_0_r, Rminus_0_r.
    apply sqrt_def.
    lra.
  Qed.

Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv];
  try nonzero.
Ltac R_field := R_field_simplify; reflexivity.
Ltac C_field_simplify := repeat field_simplify_eq [Csqrt2_square Csqrt2_inv];
  try nonzero.
Ltac C_field := C_field_simplify; reflexivity.

Lemma Csum_extend_r : forall n f, Csum f n + f n = Csum f (S n).
Proof. reflexivity. Qed.

Lemma Csum_extend_l : forall n f, f O + Csum (fun x => f (S x)) n = Csum f (S n).
Proof.
  intros n f.
  induction n.
  + simpl. lca.
  + simpl.
    rewrite <- Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
Qed.

Lemma Cmult_plus_dist_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_plus_dist_r (x y z : C) : (x + y) * z = x * z + y * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Csum_sum : forall m n f, Csum f (m + n) =
                          Csum f m + Csum (fun x => f (m + x)%nat) n.
Proof.
  intros m n f.
  induction m.
  + simpl. rewrite Cplus_0_l. reflexivity.
  + simpl.
    rewrite IHm.
    remember (fun y => f (m + y)%nat) as g.
    replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
    replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
    replace (Csum (fun x : nat => f (S (m + x))) n) with
            (Csum (fun x : nat => g (S x)) n).
    2:{ apply Csum_eq. subst. intros. intros; rewrite <- plus_n_Sm. reflexivity. }
    repeat rewrite Cplus_assoc.
    rewrite Csum_extend_l.
    rewrite Csum_extend_r.
    reflexivity.
Qed.
Lemma Csum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof.
  intros f g n H.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.
Lemma Csum_product : forall m n f g, n <> O ->
                              Csum f m * Csum g n =
                              Csum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n).
Proof.
  intros.
  induction m.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_dist_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n).
    2:{
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.

Opaque C.

(* --- Matrices *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Import List.

Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Open Scope nat_scope.

Definition Matrix (m n : nat) := nat -> nat -> C.

Bind Scope matrix_scope with Matrix.
Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

Notation "[ ]" := nil (format "[ ]") : list_scope.

Definition l2V (l : list C) : Vector (length l) :=
  (fun x y => nth x l 0%R).
Definition l2M (l : list (list C)) : Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).

Arguments l2V l i j /.

Arguments l2M l i j /.

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.
Infix "==" := mat_equiv (at level 80).

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. 
  intros m n A i j Hi Hj. 
  reflexivity. 
Qed.

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = 0%C. 

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C-> A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
    A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

Close Scope nat_scope.
Open Scope C_scope.

Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.
Open Scope matrix_scope.

Open Scope matrix_scope.
Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.
Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0.
Definition Mscale {m n : nat} (c : C) (A : Matrix m n) : Matrix m n :=
  fun i j => c * A i j.
Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.
Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "*" := Mscale (at level 40, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A + B) + C == A + (B + C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A + B == B + A.
Proof.
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n + A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lca.
Qed.

Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A + Zero m n == A.
Proof.
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
    A == A' -> B == B' -> A + B == A' + B'.
Proof.
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA by lia.
  rewrite HB by lia.
  reflexivity.
Qed.

Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; easy.
Qed.


Lemma Mplus3 : forall {m n} (A B C : Matrix m n), (B + A) + C == A + (B + C).
Proof.
  intros m n A B C.
  rewrite (Mplus_comm B A). 
  apply Mplus_assoc.
Qed.

Lemma Mscale_compat : forall {m n} (c c' : C) (A A' : Matrix m n),
    c = c' -> A == A' -> c * A == c' * A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; easy.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; easy.
Qed.

Definition trace {n : nat} (A : Square n) : C :=
  Csum (fun x => A x x) n.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
  fun x z => Csum (fun y => A x y * B y z)%C n.

Open Scope nat_scope.

Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) :
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => (A y x)^*.

Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
    Mmult (transpose A) B 0 0.
Definition inner_product {n} (u v : Vector n) : C :=
    Mmult (adjoint u) (v) 0 0.

Definition outer_product {n} (u v : Vector n) : Square n :=
    Mmult u (adjoint v).
    
Close Scope nat_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope.
Notation "A †" := (adjoint A) (at level 0) : matrix_scope.
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  unfold trace.
  apply Csum_eq.
  intros x Hx.
  rewrite H; easy.
Qed.


Add Parametric Morphism n : (@trace n)
  with signature mat_equiv ==> eq as trace_mor.
Proof. intros; apply trace_compat; easy. Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' H1 H2 i j Hi Hj.
  unfold "×".
  apply Csum_eq.
  intros x Hx.
  rewrite H1, H2; easy.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Lemma kron_compat : forall {m n o p} (A A' : Matrix m n) (B B' : Matrix o p),
    A == A' -> B == B' -> A ⊗ B == A' ⊗ B'.
Proof.
  intros m n o p A A' B B' HA HB.
  intros i j Hi Hj.
  unfold kron.
  assert (Ho : o <> O). intros F. rewrite F in *. lia.
  assert (Hp : p <> O). intros F. rewrite F in *. lia.
  rewrite HA, HB. easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.div_lt_upper_bound; lia.
  - apply Nat.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism m n o p : (@kron m n o p)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof. intros. apply kron_compat; easy. Qed.

Lemma transpose_compat : forall{m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.

Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o)
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p A B C i j Hi Hj.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lca.
  + simpl.
    rewrite <- IHn.
    simpl.
    rewrite Csum_mult_l.
    rewrite <- Csum_plus.
    apply Csum_eq; intros.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Csum_conj_distr : forall (f : nat -> C) (n : nat),
    (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof.
Admitted.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† == B† × A†.
Proof.
  intros m n o A B i j Hi Hj.
  unfold Mmult, adjoint.
  rewrite Csum_conj_distr.
  apply Csum_eq; intros.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma adjoint_involutive : forall {m n} (A : Matrix m n), A†† == A.
Proof.
  intros m n A i j _ _.
  lca.
Qed.

Lemma kron_adjoint : forall {m n o p} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† == A† ⊗ B†.
Proof.
  intros m n o p A B.
  intros i j Hi Hj.
  unfold adjoint, kron.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

Ltac by_cell :=
  intros;
  let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lca.

Lemma scale0_concrete : 0 * I 10 == Zero _ _.
Proof. lma. Qed.

Lemma id_kron : forall {m n : nat}, I m ⊗ I n == I (m * n).
Proof.
  intros. intros i j Hi Hj.
  unfold I, kron.
  destruct (i =? j) eqn:E. apply Nat.eqb_eq in E. subst.
  - rewrite <- 2 beq_nat_refl. lca.
  - destruct (i / n =? j / n) eqn:E1; destruct (i mod n =? j mod n) eqn:E2;
      try lca; try lia.
    apply Nat.eqb_eq in E1.
    apply Nat.eqb_eq in E2.
    apply Nat.eqb_neq in E.
    contradict E.
    assert (n * m <> 0)%nat as Hnm by lia.
    apply Nat.neq_mul_0 in Hnm as [Hn _].
    rewrite (Nat.div_mod i n) by assumption.
    rewrite (Nat.div_mod j n) by assumption.
    rewrite E1, E2.
    reflexivity.
Qed.

Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 * A == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_0_r : forall {m n : nat} (c : C), c * Zero m n == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 * A == A.

Proof. intros. lma. Qed.
Lemma Mscale_1_r : forall {n : nat} (c : C),
    c * I n == fun x y => if (x =? y) then c else 0.
Proof.
  intros n c i j _ _.
  unfold I, Mscale; simpl.
  destruct (i =? j); lca.
Qed.

Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), Zero m n × A == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.

Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × Zero n o == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n),
  I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hi.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Hx.
  lca.
Qed.

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n),
  A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hj.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx.
  lca.
Qed.

Lemma kron_0_l : forall {m n o p : nat} (A : Matrix o p),
  Zero m n ⊗ A == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_0_r : forall {m n o p : nat} (A : Matrix m n),
   A ⊗ Zero o p == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), I 1 ⊗ A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.mod_small by lia.
  rewrite 2 Nat.div_small by lia.
  simpl; lca.
Qed.

Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.

Lemma kron_1_r' : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 = A.
Proof.
  intros m n A.
  unfold I, kron.
  apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.

Lemma kron_1_l_inv : forall {m n} (A : Matrix m n),
  A == I 1 ⊗ A.
Proof.
  intros.
  specialize (kron_1_l A) as G.
  rewrite 2 Nat.mul_1_l in *.
  symmetry.
  apply G.
Qed.

Lemma kron_1_r_inv : forall {m n} (A : Matrix m n),
  A == A ⊗ I 1.
Proof.
  intros.
  specialize (kron_1_r A) as G.
  rewrite 2 Nat.mul_1_r in *.
  symmetry.
  apply G.
Qed.

Lemma id_transpose_eq : forall {n : nat}, (I n)⊤ == (I n).
Proof.
  intros. by_cell.
  unfold transpose, I.
  rewrite Nat.eqb_sym.
  reflexivity.
Qed.

Lemma zero_transpose_eq : forall {m n : nat}, (@Zero m n)⊤ == @Zero m n.
Proof. reflexivity. Qed.

Lemma id_adjoint_eq : forall {n : nat}, (I n)† == (I n).
Proof.
  by_cell.
  unfold adjoint, I.
  rewrite Nat.eqb_sym.
  destruct (i =? j); lca.
Qed.

Lemma zero_adjoint_eq : forall {m n : nat}, (@Zero m n)† == @Zero n m.
Proof.
  unfold adjoint, Zero.
  rewrite Cconj_0.
  reflexivity.
Qed.

Lemma Mplus_adjoint : forall {m n : nat} (A : Matrix m n) (B : Matrix m n),
  (A + B)† == A† + B†.
Proof. lma. Qed.

Lemma Mscale_assoc : forall {m n : nat} (x y : C) (A : Matrix m n),
  x * (y * A) == (x * y)%C * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_l : forall {m n : nat} (x y : C) (A : Matrix m n),
  (x + y)%C * A == x * A + y * A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_r : forall {m n : nat} (x : C) (A B : Matrix m n),
  x * (A + B) == x * A + x * B.
Proof. lma. Qed.

Lemma Mmult_plus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o),
                           A × (B + C) == A × B + A × C.
Proof.
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_dist_l.
  reflexivity.
Qed.
Lemma Mmult_plus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o),
                           (A + B) × C == A × C + B × C.
Proof.
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_dist_r.
  reflexivity.
Qed.

Lemma kron_plus_dist_l : forall {m n o p : nat} (A : Matrix m n) (B C : Matrix o p),
                           A ⊗ (B + C) == A ⊗ B + A ⊗ C.
Proof.
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_dist_l.
  reflexivity.
Qed.
Lemma kron_plus_dist_r : forall {m n o p : nat} (A B : Matrix m n) (C : Matrix o p),
                           (A + B) ⊗ C == A ⊗ C + B ⊗ C.
Proof.
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_dist_r.
  reflexivity.
Qed.
Lemma Mscale_mult_dist_l : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o),
    ((x * A) × B) == x * (A × B).
Proof.
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.
Lemma Mscale_mult_dist_r : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x * B)) == x * (A × B).
Proof.
  intros. intros i j _ _.
  unfold Mscale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.
Lemma Mscale_kron_dist_l : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p),
    ((x * A) ⊗ B) == x * (A ⊗ B).
Proof. lma. Qed.
Lemma Mscale_kron_dist_r : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p),
    (A ⊗ (x * B)) == x * (A ⊗ B).
Proof. lma. Qed.
Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q )
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) == (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D i j _ _.
  unfold kron, Mmult.
  destruct q.
  + simpl.
    rewrite mult_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity.
  + rewrite Csum_product by lia.
    apply Csum_eq_bounded. intros.
    lca.
Qed.
(*******************************)
(* Automation *)
(*******************************)
Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat.
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]] => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]] => rewrite plus_0_l
  | [ |- context[ (?a + 0)%nat]] => rewrite plus_0_r
  | [ |- context[ (1 * ?a)%nat]] => rewrite Nat.mul_1_l
  | [ |- context[ (?a * 1)%nat]] => rewrite Nat.mul_1_r
  | [ |- context[ (2 * 2^?x)%nat]] => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]] => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]] => rewrite double_pow
  | [ |- context[ (2^?x * 2^?y)%nat]] => rewrite <- Nat.pow_add_r
  | [ |- context[ (?a + (?b + ?c))%nat ]] => rewrite plus_assoc
  | [ |- (2^?x = 2^?y)%nat ] => apply pow_components; try lia
  end.

Ltac is_nat_equality :=
    match goal with
    | |- ?A = ?B => match type of A with
                  | nat => idtac
                  end
    end.
Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.
  
Ltac unify_matrix_dims tac :=
    try reflexivity;
    repeat (apply f_equal_gen; try reflexivity;
            try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
  match A with
  (* special cases *)
    | ?A × I _ => let A' := restore_dims_rec A in
                          match type of A' with
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                          end
    | I _ × ?B => let B' := restore_dims_rec B in
                          match type of B' with
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n') B')
                          end
    | ?A × @Zero ?n ?n => let A' := restore_dims_rec A in
                          match type of A' with
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                          end
    | @Zero ?n ?n × ?B => let B' := restore_dims_rec B in
                          match type of B' with
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                          end
    | ?A × @Zero ?n ?o => let A' := restore_dims_rec A in
                          match type of A' with
                          | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                          end
    | @Zero ?m ?n × ?B => let B' := restore_dims_rec B in
                          match type of B' with
                          | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                          end
    | ?A + @Zero ?m ?n => let A' := restore_dims_rec A in
                          match type of A' with
                          | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                          end
    | @Zero ?m ?n + ?B => let B' := restore_dims_rec B in
                          match type of B' with
                          | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                          end
  (* general cases *)
    | ?A == ?B => let A' := restore_dims_rec A in
                  let B' := restore_dims_rec B in
                  match type of A' with
                  | Matrix ?m' ?n' => constr:(@mat_equiv m' n' A' B')
                    end
    | ?A × ?B => let A' := restore_dims_rec A in
                  let B' := restore_dims_rec B in
                  match type of A' with
                  | Matrix ?m' ?n' =>
                    match type of B' with
                    | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                    end
                  end
    | ?A ⊗ ?B => let A' := restore_dims_rec A in
                  let B' := restore_dims_rec B in
                  match type of A' with
                  | Matrix ?m' ?n' =>
                    match type of B' with
                    | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                    end
                  end
    | ?A † => let A' := restore_dims_rec A in
                  match type of A' with
                  | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                  end
    | ?A + ?B => let A' := restore_dims_rec A in
                 let B' := restore_dims_rec B in
                 match type of A' with
                 | Matrix ?m' ?n' =>
                   match type of B' with
                   | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                   end
                 end
    | ?c * ?A => let A' := restore_dims_rec A in
                 match type of A' with
                 | Matrix ?m' ?n' => constr:(@Mscale m' n' c A')
                 end
    (* Handle functions applied to matrices *)
    | ?f ?A => let f' := restore_dims_rec f in
                 let A' := restore_dims_rec A in
                 constr:(f' A')
    (* default *)
    | ?A => A
     end.

Ltac restore_dims tac :=
    match goal with
    | |- ?A => let A' := restore_dims_rec A in
                  replace A with A' by unify_matrix_dims tac
    end.
  
Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (try ring; unify_pows_two; simpl; lia).
  (*************************)
  (* Matrix Simplification *)
  (*************************)
Hint Unfold Mplus Mmult Mscale kron adjoint I : U_db.

Hint Rewrite @kron_1_l @kron_1_r' @Mmult_1_l @Mmult_1_r @Mscale_1_l
       @id_adjoint_eq @id_transpose_eq : M_db_light.

Hint Rewrite @kron_0_l @kron_0_r @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
       @Mscale_0_l @Mscale_0_r @zero_adjoint_eq @zero_transpose_eq : M_db_light.
  (* I don't like always doing restore_dims first, but otherwise sometimes leaves 
     unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := restore_dims; autorewrite with M_db_light.
  
Hint Rewrite @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
       @adjoint_involutive : M_db.
  
Ltac Msimpl := restore_dims; autorewrite with M_db_light M_db;
    repeat match goal with
    | [|- context[I 1 ⊗ ?A]] => rewrite (kron_1_l A)
    | [|- context[I 1 ⊗ ?A]] => rewrite <- (kron_1_l_inv A)
    end.

(* Quantum *)
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import List.
Import ListNotations.

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
