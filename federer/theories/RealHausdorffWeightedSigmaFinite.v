(** Federer (1969), 2.10.24, pp. 187–188: the Hausdorff weighted-integral
    equality when the positive support has a countable finite-measure cover.
    Retain the actual Gamma normalization in every nonnegative real degree.
    Reuse the existing generic Borel restriction and Fatou arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffMeasureLaws RealPowerCoverVariants MetricRealPowerCost MetricRealPowerClosedCovers MetricRealPowerMeasure
  CaratheodoryLimitUP RealHausdorffEnlargement RealSphericalEnlargement ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureBasic MeasureAlmostBasic MeasureFiniteClosure MeasureIntegralBounds BorelRegularMeasureUP
  TopologicalBorel MetricDiameter MetricDiameterClosure HausdorffLengthUP HausdorffMeasureUP
  HausdorffMeasureLaws HausdorffMeasure HausdorffClosedCovers HausdorffClosedCoverAgreement HausdorffDiameterCost
  CaratheodoryBorelRegular CaratheodoryUniformBorelApproximation BorelFiniteIncreasingCover ClosedHausdorffEnlargementUP ClosedHausdorffEnlargement
  WeightedMetricLimit WeightedMeasurableHullBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_actual_closed_generator_laws]: supporting
    closed-generator realization of the actual Hausdorff
    measure for 2.10.24, p. 188, from the
    proved closed-cover agreement of 2.10.2(1), p. 171. *)
Lemma real_hausdorff_actual_closed_generator_laws (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R) :
  is_caratheodory_limit (fun j : @nonempty_closed_metric_sets R X => val j)
    (fun j => metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j))
    (@real_hausdorff_measure R X p hp).
Proof.
have he : @real_hausdorff_measure R X p hp=
    @closed_metric_real_power_measure R X (real_hausdorff_normalisation hp) p.
  apply: funext => A; exact: real_hausdorff_closed_cover_equality.
rewrite he; exact: closed_metric_real_power_measure_specification.
Qed.

(** Source for [real_hausdorff_uniform_closed_hull_restrictions]:
    supporting B_j construction in 2.10.24(1),
    p. 187, applied to Hausdorff measure as on
    p. 188. The uniform bounds hold for closures
    of the original arbitrary nonempty generators;
    their diameters and costs are unchanged. *)
Theorem real_hausdorff_uniform_closed_hull_restrictions (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (f : X -> \bar R) (A : nat -> set X) :
  (forall n, (@real_hausdorff_measure R X p hp) (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  has_uniform_measurable_hull_restrictions (@real_hausdorff_measure R X p hp)
    (fun j : @nonempty_metric_sets R X=>val j) (fun j=>closure (val j))
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) f.
Proof.
move=> hAfin hsupport t ht.
pose psi := @real_hausdorff_measure R X p hp.
pose F := [set S : set X | closed S /\ S!=set0].
have hclosedlaws := @real_hausdorff_actual_closed_generator_laws R X p hp.
have hm := @real_hausdorff_measure_is_measure R X p hp.
have hc (j : @nonempty_closed_metric_sets R X) := @metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p (val j) (ltW (real_hausdorff_normalisation_positive hp)).
have hr := caratheodory_limit_borel_regular hclosedlaws hc (fun j=>closed_borel_set (set_valP j).1).
have [D [hD [hDfinite [hDinc hAD]]]] := @borel_finite_increasing_cover R X psi A hm hr hAfin.
have [B [r [hB [hBinc [hBD [hnull [hrpos hlocal]]]]]]] :=
  @caratheodory_increasing_borel_generator_bounds R X F (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) psi
    (@closed_hausdorff_enlargement R X 1) (@real_hausdorff_enlargement_control R p) D (fun _=>t)
    (@real_closed_hausdorff_enlargement_specification R X (real_hausdorff_normalisation hp) p (ltW (real_hausdorff_normalisation_positive hp)) hp) hclosedlaws (fun S hS=>hS.1) hD hDfinite hDinc (fun _=>ht).
have hnullf : psi ([set x | 0<f x] `\` \bigcup_n B n)=0.
  apply: (@measure_null_subset R X psi hm _ _ _ hnull)=> x [hx hxB]; split=> //.
  exact: hAD x (hsupport x hx).
exists B,r; split=> //; split=> //; split=> //; split.
- move=> n j; apply: (@measure_measurable_intersection R X psi hm).
  + exact: (@borel_regular_borel_measurable R X psi hm hr (B n) (hB n)).
  + exact: (@borel_regular_borel_measurable R X psi hm hr _ (closed_borel_set (@closed_closure X (val j)))).
- move=> n j hdj.
  have hT : F (closure (val j)) := @nonempty_closed_hull_member R X j.
  have hdiam : extended_metric_diameter (closure (val j))<=(r n)%:E by rewrite extended_metric_diameter_closure.
  have hh := hlocal n (closure (val j)) hT hdiam.
  by rewrite metric_real_diameter_cost_closure in hh.
Qed.

(** Source for [real_hausdorff_weighted_sigma_finite_equality]:
    real-degree Hausdorff instance of the first
    equality criterion in 2.10.24, p. 187,
    for the construction mentioned on p. 188.
    The ambient metric space is arbitrary; only
    the positive support needs the stated finite-measure
    cover. Cover members and f may be nonmeasurable. *)
Theorem real_hausdorff_weighted_sigma_finite_equality (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (f : X -> extended_real_line R) (A : nat -> set X) :
  (forall x, 0<=f x) -> (forall n, (@real_hausdorff_measure R X p hp) (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_hausdorff_measure R X p hp) f=
      measure_upper_integral (@real_hausdorff_measure R X p hp) (partial_function_total f).
Proof.
move=> hf hAfin hcover.
pose J := @nonempty_metric_sets R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := @metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p (val j).
pose psi := @real_hausdorff_measure R X p hp.
pose L := @weighted_metric_limit R X J S c psi.
exact: (@weighted_measurable_hull_integral_equality R X (@nonempty_metric_sets R X)
  (@real_hausdorff_measure R X p hp) (fun j=>val j) (fun j=>closure (val j))
  (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) L f
  (@real_hausdorff_measure_is_measure R X p hp) (fun j=>@metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p (val j) (ltW (real_hausdorff_normalisation_positive hp)))
  (fun j x hx=>subset_closure hx) hf (@real_hausdorff_measure_specification R X p hp)
  (@weighted_metric_limit_specification R X J S c psi)
  (@real_hausdorff_uniform_closed_hull_restrictions R X p hp f A hAfin hcover)).
Qed.
