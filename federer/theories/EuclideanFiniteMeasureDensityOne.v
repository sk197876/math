(** Federer (1969), 3.3.17, pp. 300–301: actual
    relative density one on EVERY original finite-measure source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanFiniteMeasureVitali
  MeasureDerivationContext MeasureRestriction MeasureDensityPoints DensityMeasurableSets
  MeasureDerivates CenteredBallRelations PartialFunctionUP MeasureAlmostUP
  MetricDensityOneUpperAgreement MetricDensities MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_finite_measure_restriction_density_one]:
    the actual 2.9.11 appeal in Federer 3.3.17, pp. 300–301.
    Finite whole mass supplies the actual centered-ball Vitali
    context through the proved Euclidean directional limitation.
    Actual 2.9.11 gives relative derivate one at psi almost every
    point of the ORIGINAL arbitrary A. Source measurability is
    not a premise and no measurable hull replaces A. *)
Lemma euclidean_finite_measure_restriction_density_one (R:realType) n
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_derivation_measure psi ->psi setT< +oo ->
  measure_almost_everywhere_on psi A [set a|
    partial_function_graph (measure_derivate (measure_restrict psi A) psi
      (@centered_closed_ball_relation R (inner_metric_space (@euclidean_inner_productP R n)))) a 1].
Proof.
move=>hPsi hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hContext:is_measure_derivation_context psi (@centered_closed_ball_relation R [the metricType R of X]).
  constructor; first exact:hPsi.
  exact:(@euclidean_finite_measure_centered_vitali R n psi
    (derivation_measure_law hPsi) (derivation_measure_borel_regular hPsi) hFinite).
exact:(@density_one_points_conclusions R [the metricType R of X] psi
  (@centered_closed_ball_relation R [the metricType R of X]) A hContext).2.1.
Qed.

(** Source for [euclidean_finite_measure_restriction_upper_density_agreement]:
    the exact upper-density equality in the proof of Federer 3.3.17,
    pp. 300–301. At psi almost every point of the original arbitrary A,
    restricting psi to A preserves the original upper density, including
    infinite density. The actual relative density-one theorem supplies
    the premise; no measurability of A is required. *)
Lemma euclidean_finite_measure_restriction_upper_density_agreement (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_derivation_measure psi ->psi setT< +oo ->
  measure_almost_everywhere_on psi A [set a|
    upper_metric_density m (measure_restrict psi A) a=upper_metric_density m psi a].
Proof.
move=>hPsi hFinite.
have hOne:=@euclidean_finite_measure_restriction_density_one R n psi A hPsi hFinite.
apply:(@measure_null_subset R _ psi (derivation_measure_law hPsi) _ _ _ hOne).
move=>a [hA hNot]; split; first exact:hA.
move=>hAt; apply:hNot.
apply:(@metric_density_one_upper_agreement R _ m psi (measure_restrict psi A) a hPsi).
- exact:(@measure_restrict_is_measure R _ psi (derivation_measure_law hPsi) A).
- move=>S; apply:(@measure_mono R _ psi (derivation_measure_law hPsi)); by move=>x [_ hx].
- exact:hAt.
Qed.
