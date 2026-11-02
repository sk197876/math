(** Federer (1969), 2.10.47, p. 204: substitute
    the power diameter gauge into the finite cube-cover
    estimate. The coefficient c is explicit and the
    exponent p is real; no Gamma normalisation is needed
    for these homogeneous covering inequalities. Source
    editions: DyadicSmallSetCover.v and MetricRealPowerCost.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicContentCutoffLower DyadicLevelCostBound
  RefiningCoverContent MetricDiameterUP MetricDiameter MetricRealPowerCost RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_power_content_level_bound]: supporting
    estimate 2^n c (sqrt(n) 2^(-j))^p in
    2.10.47, p. 204. This includes p=0 and
    diameter-zero source sets; c need only be nonnegative. *)
Theorem dyadic_power_content_level_bound (R : realType) n (a : R_n R n) Q c p i gamma j
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  (0<=c)%R -> (0<=p)%R -> (i<=j)%N -> S!=set0 ->
  (forall x, S x -> forall l, (a l<=x l<=a l+1)%R) ->
  extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E ->
  gamma S<=(((2^n)%N)%:R*(c*real_power (Num.sqrt n%:R/((2^j)%N)%:R) p))%:E.
Proof.
move=> hQ hg hc hp hij hne hroot hd.
apply: (@dyadic_level_content_bound R n a Q _ i gamma j S _ hQ hg _ hij _ _ hne hroot hd).
- move=> T _; exact: metric_real_power_cost_nonnegative hc.
- exact: mulr_ge0 hc (real_power_nonnegative _ _).
- move=> s; rewrite /metric_real_diameter_cost -metric_real_power_cost_finite.
  apply: metric_real_power_cost_monotone hc hp _ (@dyadic_cube_extended_diameter_bound R n a Q hQ j s).
  exact: metric_diameter_nonnegative (extended_metric_diameter_specification _).
Qed.
