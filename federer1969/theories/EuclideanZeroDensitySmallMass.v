(** Federer (1969), 3.1.2, p. 212: density zero supplies arbitrarily small
    relative mass in every sufficiently small centered ball. This is the
    measure estimate used to prove uniqueness of the approximate differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanNoncenteredVitali EuclideanClosedBallVolume CenteredBallRelations
  MetricClosedBalls MetricDiameter MetricDiameterUP CoveringFamilyUP
  PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction MeasureSetDensity
  MeasureDerivates CoveringFiniteLimitBounds MeasureRatioComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_zero_density_small_mass]: the first strict
    measure inequality in the uniqueness argument of Federer 3.1.2,
    p. 212. The arbitrary positive fraction is later chosen from the
    smaller ball's volume. No measurability of the exceptional set is needed. *)
Theorem euclidean_zero_density_small_mass (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) a :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]) A) a 0 ->
  forall c : R, (0<c)%R -> exists d : R, (0<d)%R /\ forall r : R,
    (0<r)%R -> (r<d)%R ->
    euclidean_lebesgue_measure n (A `&` metric_closed_ball a r) <
      c%:E * euclidean_lebesgue_measure n (metric_closed_ball a r).
Proof.
move=> hA c hc.
have [b [hb hsmall]] := @covering_finite_limit_small_values R _ _ _ a 0 c hA hc.
exists (b/3)%R; split; first by rewrite divr_gt0 // ltr0n.
move=> r hr hrd.
pose S := metric_closed_ball a r.
have hS : centered_closed_ball_relation a S by exists r.
have hdiam : extended_metric_diameter S<b%:E.
  have hd : extended_metric_diameter S <= (r+r)%R%:E.
    apply: (metric_diameter_least (extended_metric_diameter_specification S)).
    - rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
    - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
  apply: le_lt_trans hd _; rewrite lte_fin.
  have : (r*3<b)%R by move: hrd; rewrite ltr_pdivlMr ?ltr0n.
  lra.
have hp := @euclidean_closed_ball_positive R n a r hr.
have hf : euclidean_lebesgue_measure n S \is a fin_num.
  by rewrite /S euclidean_closed_ball_normalized_volume ?ltW // fin_numE.
have hm := euclidean_lebesgue_is_measure R n.
have hfa : euclidean_lebesgue_measure n (A `&` S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  apply: le_lt_trans (@measure_mono R _ _ hm (A `&` S) S (fun x hx=>hx.2)) _.
  by rewrite /S euclidean_closed_ball_normalized_volume ?ltW // ltry.
have hq := @measure_ratio_positive_finite_denominator R _
  (measure_restrict (@euclidean_lebesgue_measure R n) A)
  (@euclidean_lebesgue_measure R n) S hp hf.
have hlt := (hsmall S _ hS hdiam hq).2; rewrite add0r in hlt.
exact: (@finite_measure_ratio_comparison R _ _ _ S c _ hfa hf hp hq hlt).
Qed.
