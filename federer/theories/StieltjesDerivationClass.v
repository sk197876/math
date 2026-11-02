(** Federer (1969), 2.9.19, pp. 163–164: the two Radon measures induced by a
    real function of locally bounded variation satisfy the class-M
    hypotheses needed for the almost-everywhere derivate theorem 2.9.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype normed_module.
From Federer Require Import RealMetricBackground MetricBoundedUnion MeasureUP MeasureBasic
  RadonMeasureUP BorelRegularMeasureUP MeasureDerivationContext CurveArcLength
  StieltjesImageMeasures StieltjesInducedPairLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_radon_derivation_class]: supporting class-M
    verification for the real Radon measures in Federer 2.9.19, p. 163,
    using 2.2.5, p. 62, and 2.9.1, p. 152. Every bounded scalar set lies in
    a compact segment, whose mass is finite. Borel regularity and measure
    laws remain explicit premises, not consequences attributed to compact
    finiteness alone. *)
Lemma scalar_radon_derivation_class (R : realType)
    (mu : set (real_line_metric R) -> \bar R) :
  is_measure mu -> is_radon_measure mu -> is_borel_regular_measure mu ->
  @is_derivation_measure R [the metricType R of real_line_metric R] mu.
Proof.
move=> hm hr hb; constructor=> // A hA.
have [r [hr0 hdist]] := @metric_bounded_distance_bound R
  [the metricType R of real_line_metric R] A 0 hA.
have hsub : A `<=` `[-r,r].
  move=> x hx; have hd := hdist x hx.
  rewrite real_line_metric_distanceE sub0r normrN in hd.
  by rewrite /= in_itv /= -ler_norml.
apply: le_lt_trans (@measure_mono R _ mu hm A `[-r,r] hsub) _.
exact (@radon_compact_finite R [the topologicalType of real_line_metric R] mu hr
  `[-r,r] (@segment_compact R (-r) r)).
Qed.

(** Source for [stieltjes_induced_pair_derivation_class]: supporting
    verification for every induced pair psi+,psi- in Federer 2.9.19, p. 163,
    whose construction and laws are 2.5.17, p. 111. We retain Federer's
    stronger finiteness on every bounded set, deriving it from real Radon
    compact finiteness. *)
Lemma stieltjes_induced_pair_derivation_class (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  @is_derivation_measure R [the metricType R of real_line_metric R] psip /\
  @is_derivation_measure R [the metricType R of real_line_metric R] psim.
Proof.
move=> hg hp.
have [hmp [hmm [hrp [hrm [hbp [hbm _]]]]]] := @induced_measure_pair_laws R g hg psip psim hp.
split.
- exact: scalar_radon_derivation_class hmp hrp hbp.
- exact: scalar_radon_derivation_class hmm hrm hbm.
Qed.
