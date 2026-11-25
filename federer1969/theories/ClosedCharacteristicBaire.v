(** Federer (1969), 2.2.15, p. 71: closed sets have Baire characteristic
    functions. The distance witness is sealed; the continuous cutoff variant
    is documented in ClosedSetContinuousCutoffs.v. The empty closed set is
    handled separately, so no finite distance to the empty set is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground BaireFunctions BaireRealAlgebra
  PointwiseEventuallyConstant ClosedSetContinuousCutoffs CharacteristicFunctionUP
  MetricSetDistanceSealed MetricSetDistanceBasic MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_characteristic_baire]: direct closed-set
    generator step for the family F in Federer 2.2.15,
    p. 71. A function satisfying the characteristic laws
    is the pointwise limit of continuous distance cutoffs for a
    nonempty closed set, and is constant zero for the empty set. *)
Theorem closed_characteristic_baire (R : realType) (X : metricType R)
    (A : set X) (f : X -> real_line_metric R) :
  closed A -> is_characteristic_function A f -> is_baire_function f.
Proof.
move=> hA hf; case: (pselect (A !=set0))=> [hn|hn].
- pose d := @MetricSetDistance.value R X A hn.
  have hd := @MetricSetDistance.laws R X A hn.
  apply: (@baire_function_pointwise_limit R X [the metricType R of real_line_metric R]
    (closed_distance_cutoff d) f).
  + move=> n; apply: continuous_baire_function; exact: closed_distance_cutoff_continuous hd n.
  + apply: pointwise_eventually_equal_limit=> x.
    case: (pselect (A x))=> hx.
    * exists 0%N=> n _; rewrite (characteristic_on_set hf hx).
      apply: closed_distance_cutoff_zero_distance; exact: (@metric_set_distance_member R X A d hd x hx).
    * have hpos := @metric_set_distance_positive_outside_closed R X A d hd x hA hx.
      have [N hN] := closed_distance_cutoff_eventually_zero hpos.
      exists N=> n hnn; rewrite (characteristic_off_set hf hx); exact: hN n hnn.
- have he : f = (fun _ => 0).
    apply: funext=> x.
    have hnot : ~ A x by move=> hx; apply: hn; by exists x.
    exact: (@characteristic_off_set R X A f hf x hnot).
  rewrite he; exact: baire_real_constant.
Qed.
