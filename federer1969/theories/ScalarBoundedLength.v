(** Finite scalar-section lengths supporting Federer (1969), 2.10.30, p.
    195. Bounded sections lie in finite closed intervals. This uses only the
    established scalar Lebesgue characterisation, not an external measure
    library. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure MeasureUP MeasureBasic
  MetricDiameterUP MetricDiameter MetricBoundedUnion CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_length_norm_bound]: supporting
    finite section-length bound for the bounded-set
    definition in 2.10.30, p. 195. No
    measurability of the section is assumed. *)
Lemma scalar_length_norm_bound (R : realType) (A : set (real_line_metric R)) (r : R) :
  0<=r -> (forall t, A t -> `|t|<=r) ->
  (lebesgue_scalar_measure A<=(r+r)%:E)%E.
Proof.
move=> hr hA.
have hsub : A `<=` `[-r,r].
  by move=> t ht; rewrite /= in_itv /= -ler_norml; exact: hA.
have hh := @measure_mono R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) A `[-r,r] hsub.
have hrr : -r<=r by lra.
by move: hh; rewrite (lebesgue_scalar_segment hrr) opprK.
Qed.

(** Source for [scalar_bounded_length_finite]: supporting
    finite scalar section measure for the bounded sets
    in 2.10.30, p. 195. The statement includes
    the empty set and arbitrary nonmeasurable bounded sets. *)
Lemma scalar_bounded_length_finite (R : realType) (A : set (real_line_metric R)) :
  metric_set_bounded A -> (lebesgue_scalar_measure A< +oo)%E.
Proof.
move=> hb.
have [r [hr hA]] := @metric_bounded_distance_bound R
  [the metricType R of real_line_metric R] A 0 hb.
have hnorm t : A t -> `|t|<=r.
  by move=> ht; move: (hA t ht); rewrite real_line_metric_distanceE sub0r normrN.
exact: le_lt_trans (scalar_length_norm_bound hr hnorm) (ltry _).
Qed.
