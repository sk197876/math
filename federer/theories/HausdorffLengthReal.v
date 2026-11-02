(** Federer (1969), 2.10.7, p. 175, concluding sentence: one-dimensional
    Hausdorff measure on R equals Lebesgue measure. This supplies the line
    measure in the geometric example of 2.5.10, p. 101. We prove the
    closed-segment characterization of 2.5.17, p. 111, by diameter covers
    and binary subdivision, then use its already proved uniqueness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground HausdorffLengthUP HausdorffLength
  CaratheodoryLimitUP HausdorffScaleSegments LebesgueDiameterBound
  LebesgueLineUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_length_real_segment]: segment
    length in the H^1=L^1 conclusion of Federer 2.10.7,
    p. 175, characterized by 2.5.17, p. 111.
    The point case a=b is part of the proved formula. *)
Theorem hausdorff_length_real_segment (R : realType) (a b : R) : a<=b ->
  @hausdorff_length R [the metricType R of real_line_metric R] `[a,b]=(b-a)%:E.
Proof.
move=> hab; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (caratheodory_limit_least (@hausdorff_length_specification R
    [the metricType R of real_line_metric R]))=> delta nu hp hn.
  exact (@hausdorff_scale_segment_bound R delta nu hn hp a b hab).
- have h := @lebesgue_below_hausdorff_length R `[a,b].
  by rewrite lebesgue_scalar_segment // in h.
Qed.

(** Source for [hausdorff_length_real_lebesgue_laws]:
    the characterizing laws of 2.5.17, p. 111,
    for the concluding assertion in Federer 2.10.7,
    p. 175. Borel regularity comes from the actual
    diameter construction, not an additional hypothesis. *)
Lemma hausdorff_length_real_lebesgue_laws (R : realType) :
  is_lebesgue_line_measure (@hausdorff_length R [the metricType R of real_line_metric R]).
Proof.
constructor.
- exact (@hausdorff_length_is_measure R [the metricType R of real_line_metric R]).
- exact (@hausdorff_length_borel_regular R [the metricType R of real_line_metric R]).
- exact (@hausdorff_length_real_segment R).
Qed.

(** Source for [hausdorff_length_real_eq_lebesgue]: direct
    formalisation of the concluding sentence of Federer
    2.10.7, p. 175: H^1 on the real line
    equals L^1. Equality is on all subsets, including
    nonmeasurable ones, by Borel-regular uniqueness. *)
Theorem hausdorff_length_real_eq_lebesgue (R : realType) :
  @hausdorff_length R [the metricType R of real_line_metric R]=@lebesgue_scalar_measure R.
Proof.
exact: lebesgue_line_unique (hausdorff_length_real_lebesgue_laws R)
  (lebesgue_scalar_specification R).
Qed.
