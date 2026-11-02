(** Federer (1969), 2.10.47, pp. 204–205: each fixed dyadic content is
    finite on the root cube, although the limiting Hausdorff measure can be
    infinite. The finite level-i cube cover and finite power costs prove
    this fact. It justifies the real intermediate values in step (3) and the
    finite initial pruning mass. Source context: DyadicPowerContentBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicCubeGridLaws DyadicContentCutoffLower
  RefiningCoverContent MetricDiameterUP MetricDiameter MetricRealPowerCost RealPower
  MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_power_content_root_finite]: supporting
    fixed-content finiteness in 2.10.47(3) and the
    last display on p. 205. Every subset of the
    root cube is allowed, including nonmeasurable sets. *)
Theorem dyadic_power_content_root_finite (R : realType) n (a : R_n R n) Q c p i gamma :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  (0<=c)%R -> (0<=p)%R ->
  forall E : set (inner_metric_space (@euclidean_inner_productP R n)), (forall x, E x -> forall l, (a l<=x l<=a l+1)%R) -> gamma E< +oo.
Proof.
move=> hQ hg hc hp E hE.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hcost (S : set X) : 0<=metric_real_diameter_cost c p S :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) hc.
have hm := refining_cover_content_measure hg (fun S _=>hcost S).
pose b : R := (c*real_power (Num.sqrt n%:R/((2^i)%N)%:R) p)%R.
have hgen s : gamma (@Q i s)<=b%:E.
  have ht : refining_cover_tail (dyadic_cube_level Q) i (@Q i s).
    exists i; split; first exact: leqnn; by exists s.
  apply: le_trans (refining_cover_content_generator hg ht (hcost _)) _.
  rewrite /b /metric_real_diameter_cost -metric_real_power_cost_finite.
  apply: metric_real_power_cost_monotone hc hp _ (@dyadic_cube_extended_diameter_bound R n a Q hQ i s).
  exact: metric_diameter_nonnegative (extended_metric_diameter_specification _).
have hcov : E `<=` \bigcup_s @Q i s.
  move=> x hx; have [s hs] := @dyadic_cube_level_covers R n a Q hQ i x (hE x hx).
  by exists s.
have hh := @measure_finite_indexed_cover R X (dyadic_cube_indices n i) gamma hm E (@Q i) hcov.
have hu : gamma E<=\sum_(s : dyadic_cube_indices n i) b%:E.
  apply: le_trans hh _; apply: lee_sum=> s _; exact: hgen.
apply: le_lt_trans hu _; rewrite sumEFin; exact: ltry.
Qed.
