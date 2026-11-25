(** Federer (1969), 3.2.46, p. 281: a globally
    Lipschitz representative whose image is in A supplies
    an admissible curve on every compact interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LipschitzUP LipschitzBasic RiemannianCurveCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_global_curve_admissible]: restricting
    an actual Lipschitz representative gives a curve in the
    distance infimum of Federer 3.2.46, p. 281. Its endpoints
    are its actual values, and a zero bound is allowed. *)
Lemma riemannian_global_curve_admissible (R : realType) n A
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) L a b :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C L ->
  (forall t, A (C t)) -> a <= b ->
  is_riemannian_admissible_curve A (C a) (C b) C a b.
Proof.
move=> hC hImage hab; split; first exact hab; split.
- apply: metric_lipschitz_of_bound.
  exact: metric_lipschitz_bound_restrict (fun _ _=>Logic.I) hC.
- split; first by move=> t ht; exact: hImage.
  by split.
Qed.
