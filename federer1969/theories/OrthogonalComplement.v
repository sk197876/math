(** Federer (1969), 1.7.3, p. 29: orthogonal complements. This predicate
    definition is independent of dimension and of any choice of basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Complement.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable W : subspace V.

(** Source for [orthogonal_to_subspace]: Federer 1.7.3, p. 29,
    the displayed condition defining W': x.y=0 for every y in W. *)
Definition orthogonal_to_subspace x := forall y, W y -> B x y = 0.

(** Source for [orthogonal_to_subspace_zero]: Federer 1.7.3,
    p. 29, supporting verification that W' contains zero. *)
Lemma orthogonal_to_subspace_zero : orthogonal_to_subspace 0.
Proof. by move=> y hy; rewrite (bil0l (inner_bilinear hB)). Qed.

(** Source for [orthogonal_to_subspace_add]: Federer 1.7.3,
    p. 29, supporting closure of W' under addition. *)
Lemma orthogonal_to_subspace_add x z : orthogonal_to_subspace x ->
  orthogonal_to_subspace z -> orthogonal_to_subspace (x+z).
Proof. move=> hx hz y hy; by rewrite (bilDl (inner_bilinear hB)) hx // hz // addr0. Qed.

(** Source for [orthogonal_to_subspace_scale]: Federer 1.7.3,
    p. 29, supporting closure of W' under scalar multiplication. *)
Lemma orthogonal_to_subspace_scale a x : orthogonal_to_subspace x ->
  orthogonal_to_subspace (a *: x).
Proof. move=> hx y hy; by rewrite (bilZl (inner_bilinear hB)) hx // scaler0. Qed.

(** Source for [orthogonal_complement]: Federer 1.7.3, p. 29,
    W' as a vector subspace with the displayed membership condition. *)
Definition orthogonal_complement : subspace V :=
  @Subspace R V orthogonal_to_subspace orthogonal_to_subspace_zero
    orthogonal_to_subspace_add orthogonal_to_subspace_scale.

(** Source for [orthogonal_complement_intersection_zero]: Federer
    1.7.3, p. 29, supporting orthogonal decomposition: a vector in
    both W and W' must be zero, by positive definiteness. *)
Lemma orthogonal_complement_intersection_zero x :
  W x -> orthogonal_complement x -> x = 0.
Proof.
move=> hx ho; apply/eqP; rewrite -(inner_self_eq0 hB).
by rewrite (ho x hx) eqxx.
Qed.
End Complement.
