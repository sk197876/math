(** Federer (1969), 3.2.46, p. 281: an initial
    curve segment cannot have greater length than the full
    curve. The remaining genuine integral is nonnegative. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveIntegralSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_curve_prefix_cost_bound]: the
    initial-interval length bound supporting separation and
    topology in Federer 3.2.46, p. 281. Only actual integral
    additivity and nonnegativity are used. *)
Lemma riemannian_curve_prefix_cost_bound (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b u :
  is_riemannian_admissible_curve A x y C a b -> a <= u <= b ->
  (riemannian_curve_cost g C a u <= riemannian_curve_cost g C a b)%E.
Proof.
move=> hC ht; rewrite (riemannian_curve_cost_split hg hC ht).
exact (@leeDl R (riemannian_curve_cost g C a u) (riemannian_curve_cost g C u b)
  (riemannian_curve_cost_nonnegative g C u b)).
Qed.
