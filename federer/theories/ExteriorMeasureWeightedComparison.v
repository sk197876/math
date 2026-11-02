(** Federer (1969), 2.10.37, printed p. 198: pass the positive finite
    generator-cost bound to the final covering measures. Expand the infimum
    and supremum laws of 2.10.1, pp. 169–171, rather than identifying
    different covering families by definition. The exterior family contains
    all nonempty sets, whereas the competing family may include empty
    generators. These are handled using the proved empty-measure law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffLengthUP
  ExteriorMeasureGauge ExteriorMeasureUP CaratheodoryLimitUP
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleWeightedBound
  MetricDiameter MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_measure_weighted_generator_comparison]: supporting
    passage from the convex-generator cost inequality
    to the measure inequality in 2.10.37,
    p. 198. The competing family and its
    nonnegative costs are arbitrary. Empty generators,
    arbitrary targets and infinite values are allowed. *)
Theorem exterior_measure_weighted_generator_comparison (R : realType) (n m : nat)
    (J : choiceType) (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (d : J -> \bar R)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) (a : R) :
  is_exterior_diameter_measure m mu -> is_caratheodory_limit S d nu ->
  (forall j, (0<=d j)%E) -> 0<a ->
  (forall j, (exterior_diameter_cost m (S j)<=a%:E*d j)%E) ->
  forall A, (mu A<=a%:E*nu A)%E.
Proof.
move=> hm hn hd ha hcost A.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have haE : (0<=a%:E)%E by rewrite lee_fin; exact: ltW ha.
apply: (caratheodory_limit_least hm)=> delta xi hdelta hxi.
pose eta := metric_scale_envelope S d delta.
have heta := @metric_scale_envelope_specification R E J S d delta.
have hxim := @metric_scale_envelope_is_measure R E (@nonempty_metric_sets R E)
  (fun j=>val j) (fun j=>exterior_diameter_cost m (val j)) delta xi hxi
  (fun j=>exterior_diameter_cost_nonnegative m (val j)).
have hbound : (xi A<=a%:E*eta A)%E.
  apply: (@measure_bounded_by_scaled_metric_envelope R E J S d delta eta xi a heta hxim ha).
  move=> j hj; case: (pselect (S j !=set0))=> [hne|hne].
  - pose k : @nonempty_metric_sets R E := exist _ (S j) (mem_set hne).
    have hgen := @metric_scale_generator_bound R E (@nonempty_metric_sets R E)
      (fun k=>val k) (fun k=>exterior_diameter_cost m (val k)) delta xi k hxi
      (exterior_diameter_cost_nonnegative m (S j)) hj.
    exact: le_trans hgen (hcost j).
  - have hz : S j=set0.
      apply/seteqP; split=> x; last by case.
      by move=> hx; exfalso; apply: hne; exists x.
    rewrite hz (measure_empty hxim).
    exact: mule_ge0 haE (hd j).
exact (le_trans hbound (lee_wpmul2l haE
  (@caratheodory_limit_upper R E J S d nu hn A delta eta hdelta heta))).
Qed.
