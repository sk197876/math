(** Federer (1969), 2.10.35, printed p. 197: equality of Lebesgue, Hausdorff
    and spherical measures in the ambient Euclidean dimension. The
    isodiametric bound of 2.10.33 gives the lower measure comparison by
    countable coverings; the spherical upper comparison follows the printed
    density argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanIsodiametric
  EuclideanSphericalLebesgue HausdorffLengthUP HausdorffDiameterCost HausdorffMeasure HausdorffSphericalComparison
  MetricScaleEnvelope MetricScaleEnvelopeUP MetricScaleMeasureBound CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lebesgue_hausdorff_bound]: supporting
    L^n<=H^n step in 2.10.35,
    p. 197, from 2.10.33 and
    the abstract covering infimum. No measurability
    of source sets or generators is required. *)
Theorem euclidean_lebesgue_hausdorff_bound (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (euclidean_lebesgue_measure n A<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A)%E.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose S := fun j : @nonempty_metric_sets R X=>val j.
pose c := fun j : @nonempty_metric_sets R X=>hausdorff_diameter_cost n (val j).
pose nu := metric_scale_envelope S c 1%E.
have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X) S c 1%E.
have hb : (euclidean_lebesgue_measure n A<=nu A)%E.
  apply: (@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X) S c 1%E nu
    (@euclidean_lebesgue_measure R n) hn (euclidean_lebesgue_is_measure R n))=> j hj.
  exact: lebesgue_isodiametric_bound (set_valP j).
have h1 : (0<1 :> \bar R)%E by rewrite lte_fin ltr01.
apply: le_trans hb _.
exact: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X) S c
  (@hausdorff_measure R X n) (@hausdorff_measure_specification R X n) A 1%E nu
  h1 hn).
Qed.

(** Source for [euclidean_hausdorff_spherical_lebesgue]: direct
    Hausdorff and spherical equalities in
    2.10.35, p. 197, for all
    targets, including empty sets and infinite mass. *)
Theorem euclidean_hausdorff_spherical_lebesgue (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A=euclidean_lebesgue_measure n A /\
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A=euclidean_lebesgue_measure n A.
Proof.
have hLH := euclidean_lebesgue_hausdorff_bound A.
have hHS := @hausdorff_measure_le_spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A.
have hSL := euclidean_spherical_measure_lebesgue_bound A.
split; apply/eqP; rewrite eq_le; apply/andP; split=> //.
- exact: le_trans hHS hSL.
- exact: le_trans hLH hHS.
Qed.
