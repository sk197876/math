(** Federer (1969), 1.7.3, p. 29: the subspace orthogonal to the axes
    preceding e_i. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP Bilinear ModuleQuotient
  OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Constraint.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Variable i : 'I_n.

(** Source for [orthogonal_to_predecessors]: Federer 1.7.3,
    p. 29, the linear constraints in C_i, without the unit-norm condition. *)
Definition orthogonal_to_predecessors x :=
  forall j : 'I_n, (j < i)%N -> B x (e j) = 0.

(** Source for [orthogonal_to_predecessors_zero]: Federer 1.7.3,
    p. 29, supporting zero membership for the constraint subspace. *)
Lemma orthogonal_to_predecessors_zero : orthogonal_to_predecessors 0.
Proof. by move=> j hj; rewrite (bil0l (inner_bilinear hB)). Qed.

(** Source for [orthogonal_to_predecessors_add]: Federer 1.7.3,
    p. 29, supporting closure of the constraints under addition. *)
Lemma orthogonal_to_predecessors_add x y : orthogonal_to_predecessors x ->
  orthogonal_to_predecessors y -> orthogonal_to_predecessors (x+y).
Proof. move=> hx hy j hj; by rewrite (bilDl (inner_bilinear hB)) hx // hy // addr0. Qed.

(** Source for [orthogonal_to_predecessors_scale]: Federer 1.7.3,
    p. 29, supporting closure under scalar multiplication. *)
Lemma orthogonal_to_predecessors_scale a x : orthogonal_to_predecessors x ->
  orthogonal_to_predecessors (a*:x).
Proof. move=> hx j hj; by rewrite (bilZl (inner_bilinear hB)) hx // scaler0. Qed.

(** Source for [principal_axis_constraint]: Federer 1.7.3,
    p. 29, the vector subspace whose unit sphere is C_i. *)
Definition principal_axis_constraint : subspace V :=
  @Subspace R V orthogonal_to_predecessors orthogonal_to_predecessors_zero
    orthogonal_to_predecessors_add orthogonal_to_predecessors_scale.

(** Source for [orthonormal_axis_in_constraint]: Federer 1.7.3,
    p. 29, every axis from i onward is orthogonal to the predecessors
    of i; this supplies both comparison vectors in the maximum argument. *)
Lemma orthonormal_axis_in_constraint : orthonormal_family B e ->
  forall j : 'I_n, (i <= j)%N -> principal_axis_constraint (e j).
Proof.
move=> he j hij a hai.
have haj : (a < j)%N := leq_trans hai hij.
have hja : j != a by apply/eqP=> h; move: haj; rewrite h ltnn.
by rewrite he (negbTE hja).
Qed.
End Constraint.
