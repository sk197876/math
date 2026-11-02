(** Federer (1969), 2.10.29, p. 194: the local product-measure bound, with
    an arbitrarily small coefficient, forces infinite Hausdorff measure.
    This supporting covering argument uses only the infimum and supremum
    laws of 2.10.1, p. 170. It applies to arbitrary generator costs, before
    choosing a real power or a normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameter CaratheodoryLimitUP
  MetricScaleEnvelope MetricScaleWeightedBound ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_vanishing_generator_density]: supporting
    final infimum argument of 2.10.29, p. 194:
    a positive competing measure and arbitrarily small
    bounds on all sufficiently small generators imply
    infinite covering measure. The competing measure
    need not have finite total mass. *)
Theorem caratheodory_vanishing_generator_density (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu nu : set X -> \bar R) (A : set X) :
  is_caratheodory_limit S cost mu -> is_measure nu ->
  0<nu A ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall j, extended_metric_diameter (S j)<=d%:E -> nu (S j)<=e%:E*cost j) ->
  mu A=+oo.
Proof.
move=> hm hn hpos hsmall.
have hb e (he : (0<e)%R) : nu A<=e%:E*mu A.
  have [d [hd hj]] := hsmall e he.
  pose xi := metric_scale_envelope S cost d%:E.
  have hxi := @metric_scale_envelope_specification R X J S cost d%:E.
  apply: le_trans (@measure_bounded_by_scaled_metric_envelope R X J S cost d%:E xi nu e
    hxi hn he hj A) _.
  apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW he.
  have hdE : 0<d%:E by rewrite lte_fin.
  exact (caratheodory_limit_upper hm A hdE hxi).
case hmu : (mu A)=> [r| |]; [|by []|].
- have hr : (0<=r)%R.
    have hh := hb 1%R ltr01; rewrite hmu mul1e in hh.
    have := lt_le_trans hpos hh; rewrite lte_fin=> hhpos; exact: ltW hhpos.
  have hz : nu A<=0.
    apply: (@extended_upper_bound_from_scaled_errors R (nu A) 0 r hr)=> e he.
    have hh := hb e he; by rewrite hmu -EFinM mulrC add0r in hh *.
  by have := lt_le_trans hpos hz; rewrite ltxx.
- have hh := hb 1%R ltr01; rewrite hmu mul1e leeNy_eq in hh.
  have := hpos; by rewrite (eqP hh) ltNge leNye.
Qed.
