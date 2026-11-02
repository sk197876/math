(** Federer (1969), 2.10.24, pp. 187–188: the Hausdorff weighted-integral
    equality when the positive support has a countable finite-measure cover.
    This treats integer degrees, as in the project's Hausdorff measure
    interface; it introduces no Gamma extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  MeasureIntegralBounds BorelRegularMeasureUP TopologicalBorel MetricDiameter MetricDiameterClosure
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasureLaws HausdorffMeasure HausdorffClosedCovers
  HausdorffClosedCoverAgreement HausdorffDiameterCost CaratheodoryBorelRegular
  CaratheodoryUniformBorelApproximation BorelFiniteIncreasingCover ClosedHausdorffEnlargementUP ClosedHausdorffEnlargement
  WeightedMetricLimit WeightedMeasurableHullBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_actual_closed_generator_laws]: supporting
    closed-generator realization of the actual Hausdorff
    measure for 2.10.24, p. 188, from the
    proved closed-cover agreement of 2.10.2(1), p. 171. *)
Lemma hausdorff_actual_closed_generator_laws (R : realType) (X : metricType R) (m : nat) :
  is_closed_hausdorff_measure m (@hausdorff_measure R X m).
Proof.
have he : @hausdorff_measure R X m=@closed_hausdorff_measure R X m.
  apply: funext=> A; exact: hausdorff_closed_measure_equality.
rewrite he; exact: closed_hausdorff_measure_specification.
Qed.

(** Source for [hausdorff_uniform_closed_hull_restrictions]:
    supporting B_j construction in 2.10.24(1),
    p. 187, applied to Hausdorff measure as on
    p. 188. The uniform bounds hold for closures
    of the original arbitrary nonempty generators;
    their diameters and costs are unchanged. *)
Theorem hausdorff_uniform_closed_hull_restrictions (R : realType) (X : metricType R) (m : nat)
    (f : X -> \bar R) (A : nat -> set X) :
  (forall n, hausdorff_measure m (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  has_uniform_measurable_hull_restrictions (@hausdorff_measure R X m)
    (fun j : @nonempty_metric_sets R X=>val j) (fun j=>closure (val j))
    (fun j=>hausdorff_diameter_cost m (val j)) f.
Proof.
move=> hAfin hsupport t ht.
pose psi := @hausdorff_measure R X m.
pose F := [set S : set X | closed S /\ S!=set0].
have hp := @hausdorff_actual_closed_generator_laws R X m.
have hm := @hausdorff_measure_is_measure R X m.
have hc (j : @nonempty_closed_metric_sets R X) := @hausdorff_diameter_cost_nonnegative R X m (val j).
have hr := caratheodory_limit_borel_regular hp hc (fun j=>closed_borel_set (set_valP j).1).
have [D [hD [hDfinite [hDinc hAD]]]] := @borel_finite_increasing_cover R X psi A hm hr hAfin.
have [B [r [hB [hBinc [hBD [hnull [hrpos hlocal]]]]]]] :=
  @caratheodory_increasing_borel_generator_bounds R X F (@hausdorff_diameter_cost R X m) psi
    (@closed_hausdorff_enlargement R X m) (closed_hausdorff_enlargement_control R m) D (fun _=>t)
    (@closed_hausdorff_enlargement_specification R X m) hp (fun S hS=>hS.1) hD hDfinite hDinc (fun _=>ht).
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
  by rewrite hausdorff_diameter_cost_closure in hh.
Qed.

(** Source for [hausdorff_weighted_sigma_finite_equality]:
    integer-degree Hausdorff instance of the first
    equality criterion in 2.10.24, p. 187,
    for the construction mentioned on p. 188.
    The ambient metric space is arbitrary; only
    the positive support needs the stated finite-measure
    cover. Cover members and f may be nonmeasurable. *)
Theorem hausdorff_weighted_sigma_finite_equality (R : realType) (X : metricType R) (m : nat)
    (f : X -> extended_real_line R) (A : nat -> set X) :
  (forall x, 0<=f x) -> (forall n, hausdorff_measure m (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R X m) f=
      measure_upper_integral (@hausdorff_measure R X m) (partial_function_total f).
Proof.
move=> hf hAfin hcover.
pose J := @nonempty_metric_sets R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := @hausdorff_diameter_cost R X m (val j).
pose psi := @hausdorff_measure R X m.
pose L := @weighted_metric_limit R X J S c psi.
exact: (@weighted_measurable_hull_integral_equality R X (@nonempty_metric_sets R X)
  (@hausdorff_measure R X m) (fun j=>val j) (fun j=>closure (val j))
  (fun j=>hausdorff_diameter_cost m (val j)) L f
  (@hausdorff_measure_is_measure R X m) (fun j=>@hausdorff_diameter_cost_nonnegative R X m (val j))
  (fun j x hx=>subset_closure hx) hf (@hausdorff_measure_specification R X m)
  (@weighted_metric_limit_specification R X J S c psi)
  (@hausdorff_uniform_closed_hull_restrictions R X m f A hAfin hcover)).
Qed.
