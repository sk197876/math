(** Federer (1969), 1.7.1, p. 28: orthonormal sequences and the coefficient
    calculations underlying Gram-Schmidt. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity Hom OneFormLinear FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_family]: Federer 1.7.1, p. 28,
    definition: each diagonal product is one and each product at
    distinct indices is zero. A finite index type records the sequence. *)
Definition orthonormal_family (R : fieldType) (V : lmodType R)
  (B : V -> V -> R) (I : finType) (e : I -> V) :=
  forall i j, B (e i) (e j) = if i == j then 1 else 0.

Section Coordinates.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_coordinate]: Federer 1.7.1, p. 28,
    supporting coordinate functional x -> x.v for a fixed v. *)
Definition inner_coordinate (v : V) : {linear V -> R^o} :=
  hom_as_linear (one_hom (inner_polarity hB v)).

(** Source for [inner_coordinateE]: Federer 1.7.1, p. 28,
    evaluation of the coordinate functional. *)
Lemma inner_coordinateE v x : inner_coordinate v x = B x v.
Proof. by rewrite /inner_coordinate hom_as_linearE one_homE inner_polarityE. Qed.

Variable I : finType.
Variable e : I -> V.
Hypothesis he : orthonormal_family B e.

(** Source for [orthonormal_diagonal]: Federer 1.7.1,
    p. 28, every vector of an orthonormal family has square length one. *)
Lemma orthonormal_diagonal i : B (e i) (e i) = 1.
Proof. by rewrite he eqxx. Qed.

(** Source for [orthonormal_distinct]: Federer 1.7.1,
    p. 28, distinct members of an orthonormal family are orthogonal. *)
Lemma orthonormal_distinct i j : i != j -> B (e i) (e j) = 0.
Proof. by move=> hij; rewrite he (negbTE hij). Qed.

(** Source for [orthonormal_independent]: Federer 1.7.1, p. 28, supporting
    independence of an orthonormal family. *)
Theorem orthonormal_independent : finite_independent e.
Proof.
apply: (finite_independent_separating (f:=fun i => inner_coordinate (e i))).
by move=> i j; rewrite inner_coordinateE he eq_sym.
Qed.

(** Source for [orthonormal_coefficient]: Federer 1.7.1, p. 28, the
    coefficient of e_i in a linear combination is its inner product with
    e_i. This is the calculation. *)
Lemma orthonormal_coefficient (c : I -> R) i :
  inner_coordinate (e i) (\sum_j c j *: e j) = c i.
Proof.
rewrite linear_sum.
under eq_bigr do rewrite linearZ inner_coordinateE he.
change ((\sum_j c j * (if j == i then 1 else 0)) = c i).
rewrite (bigD1 i) //= eqxx mulr1.
have hz : (\sum_(j | j != i) c j * (if j == i then 1 else 0)) = 0.
  apply: big1 => j hj; by rewrite (negbTE hj) mulr0.
by rewrite hz addr0.
Qed.
End Coordinates.
