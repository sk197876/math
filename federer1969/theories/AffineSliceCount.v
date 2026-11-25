(** Federer (1969), 2.10.16, p. 178, first displayed affine formula: v(W) is
    the number of points of A intersected with W. Use the existing
    extensional carrier of affine subspaces, and relate its actual point set
    to the projection fibres of 2.7.16(7), pp. 140–141. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric AffineSubspaceSpace OrthogonalProjectionFibres
  CountingMeasure MeasureUP MeasureBasic MappingMultiplicity ProjectionJointMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_slice_count]: direct v(W) in 2.10.16,
    p. 178: counting measure of the intersection with the
    actual affine point set. Noncountable intersections have value infinity. *)
Definition affine_slice_count (R : realType) (n d : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (W : affine_subspace_carrier (R_n R n) d) :=
  @counting_measure R [the choiceType of (R_n R n : Type)] (A `&` affine_points W).

(** Source for [affine_slice_count_nonnegative]: supporting
    nonnegativity of v in 2.10.16, p. 178, from the
    counting measure of 2.1.2, p. 54. *)
Lemma affine_slice_count_nonnegative (R : realType) (n d : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (W : affine_subspace_carrier (R_n R n) d) : 0<=affine_slice_count A W.
Proof. exact (@measure_nonnegative R [the choiceType of (R_n R n : Type)] _
  (counting_measure_is_measure R _) (A `&` affine_points W)). Qed.

(** Source for [affine_slice_count_projection_fibre]: direct
    relation between N(p restricted to A,y) and v(p^{-1}{y})
    in the first affine formula of 2.10.16, p. 178,
    using the fibre point-set identity of 2.7.16(7), p. 140. *)
Lemma affine_slice_count_projection_fibre (R : realType) (n d : nat) (hdn : (d<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n (n-d))
    (y : inner_metric_space (@euclidean_inner_productP R (n-d))) :
  affine_slice_count A (@projection_fibre R n d hdn p y)=projection_joint_multiplicity A (y,p).
Proof.
rewrite /affine_slice_count /projection_joint_multiplicity /mapping_multiplicity.
congr (counting_measure _); apply/seteqP; split=> x [hx hy]; split=> //.
- exact: (@projection_fibreE R n d hdn p y x).1 hy.
- exact: (@projection_fibreE R n d hdn p y x).2 hy.
Qed.
