(** Federer (1969), 2.10.2(1), p. 171: paraphrase: zero-dimensional
    Hausdorff measure equals counting measure on X. Prove singleton mass
    directly from the covering infimum, and use measurable unit atoms for
    the full counting assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  HausdorffClosedCoverAgreement MetricDiameter MetricDiameterMaps MetricScaleEnvelopeUP
  MetricScaleEnvelope CaratheodoryLimitUP NonnegativeSum NonnegativeSumSupport
  MeasureUP BorelRegularMeasureUP FiniteExceptionalBorel CountingMeasure UnitAtomCountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_zero_singleton]: supporting singleton calculation
    in Federer 2.10.2(1), p. 171 Every nonempty covering family contains a
    generator of cost one. *)
Lemma hausdorff_zero_singleton (R : realType) (X : metricType R) (x : X) :
  @hausdorff_measure R X 0 [set x] = 1.
Proof.
have hm := @hausdorff_measure_specification R X 0.
pose j : @nonempty_metric_sets R X :=
  @exist _ (fun A : set X => A \in [set A | A !=set0]) [set x]
    (mem_set (ex_intro _ x (erefl x))).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (caratheodory_limit_least hm)=> delta nu hd hn.
  have hcov : [set x] `<=` \bigcup_(k in [set j]) (val k).
    by move=> y ->; exists j.
  have hdiam k : [set j] k -> extended_metric_diameter (val k)<=delta.
    move=> ->; change (extended_metric_diameter [set x]<=delta).
    rewrite extended_metric_diameter_singleton; exact: ltW hd.
  have hh := @metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
    (fun k => val k) (fun k => hausdorff_diameter_cost 0 (val k)) delta nu hn
    [set x] [set j] (countable1 j) hdiam hcov.
  rewrite nonnegative_sum_singleton in hh; last exact: hausdorff_diameter_cost_nonnegative.
  by rewrite hausdorff_diameter_cost_zero_degree in hh.
- pose nu := metric_scale_envelope (fun k : @nonempty_metric_sets R X => val k)
    (fun k => hausdorff_diameter_cost 0 (val k)) 1.
  have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
    (fun k => val k) (fun k => hausdorff_diameter_cost 0 (val k)) 1.
  have hb : 1<=nu [set x].
    apply: (metric_scale_envelope_greatest hn)=> G hG hdiam hcov.
    have [k hk _] := hcov x (erefl x).
    have hh := @nonnegative_sum_term R (@nonempty_metric_sets R X) G
      (fun k => hausdorff_diameter_cost 0 (val k)) k hk.
    by rewrite hausdorff_diameter_cost_zero_degree in hh.
  apply: le_trans hb _; apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun k => val k) (fun k => hausdorff_diameter_cost 0 (val k)) _ hm [set x] 1 nu _ hn).
  by rewrite lte_fin ltr01.
Qed.

(** Source for [hausdorff_zero_counting_measure]: direct counting assertion
    of Federer 2.10.2(1), p. 171 This includes arbitrary infinite sets, not
    only countable sets. *)
Theorem hausdorff_zero_counting_measure (R : realType) (X : metricType R) (A : set X) :
  @hausdorff_measure R X 0 A=@counting_measure R X A.
Proof.
apply: (measurable_unit_atoms_counting_measure (@hausdorff_measure_is_measure R X 0))=> x.
- apply: (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X 0)
    (@hausdorff_measure_borel_regular R X 0)).
  exact: finite_metric_set_borel (finite_set1 x).
- exact: hausdorff_zero_singleton.
Qed.
