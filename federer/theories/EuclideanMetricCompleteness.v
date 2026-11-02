(** General topology supporting the Euclidean complete
    separable source in Federer (1969), 2.10.5,
    p. 172, for 2.2.10, p. 65. A proper
    Cauchy filter eventually belongs to one ball;
    its compact closed-ball enlargement supplies a
    convergent cluster point. This uses the locally
    proved Euclidean bounded compactness, not an
    external Euclidean completeness theorem. Source
    editions: EuclideanBoundedClosure.v and CompleteMetricUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CompleteMetricUP CompactCauchyLimits
  MetricClosedBalls MetricDiameterUP MetricDiameter EuclideanClosedDiameterCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_metric_complete]: supporting
    completeness of R^n in the continuous Suslin-image
    argument of Federer 2.10.5, p. 172. All
    dimensions, including zero, use the given Euclidean
    metric and the existential Cauchy-filter specification. *)
Theorem euclidean_metric_complete (R : realType) (n : nat) :
  is_complete_metric_space (inner_metric_space (@euclidean_inner_productP R n)).
Proof.
move=> F PF hC.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have [a hA] := proj1 (@cauchyP R E F PF) hC 1 ltr01.
pose K := @metric_closed_ball R E a 1.
have hd : (extended_metric_diameter K<=(2:R)%:E)%E.
  apply: (metric_diameter_least (extended_metric_diameter_specification K)).
  - by rewrite lee_fin ler0n.
  - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
have hK : compact K := @euclidean_closed_finite_diameter_compact R n K 2
  (@metric_closed_ball_closed R E a 1) hd.
have FF : Filter F := @filter_filter _ F PF.
have hFK : F K.
  apply: (@filterS _ F FF _ _ _ hA)=> x hx.
  rewrite ballEmdist in hx; exact: ltW hx.
have [x [_ hx]] := @compact_cauchy_filter_limit R E K F PF hK hFK hC.
by exists x.
Qed.
