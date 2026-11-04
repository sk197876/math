(** Federer (1969), 3.2.46, p. 282: original
    completed chart-measurable sets have precisely the
    ordinary Lebesgue-measurable coordinate images. This
    supporting adapter retains the original set rather than
    replacing it by a Borel hull. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianReferencePushforward
  MeasureUP MeasureRestriction MeasurePushforward PushforwardMeasurableSets
  MeasurableRestrictionTransfer BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [riemannian_reference_coordinate_image_measurable]:
    measurability of the actual coordinate image, supporting
    3.2.46, p. 282. Injectivity of the chart inclusion
    and measurability of its original open range suffice;
    finite mass and Borel source sets are unnecessary. *)
Theorem riemannian_reference_coordinate_image_measurable (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (S : set (riemannian_metric_space hg)) :
  measure_measurable (@riemannian_chart_reference R m A g hg) S ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    ((fun x : riemannian_metric_space hg=>val x) @` S).
Proof.
move=> hS.
pose X := [the choiceType of riemannian_metric_space hg].
pose E := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)].
pose v := fun x : X=>(val x : E).
pose T := v @` S.
have hPreimage : v @^-1` T=S.
  apply/seteqP; split=> x.
  - move=> [y hy hEq]; have hxy : x=y := val_inj (esym hEq); by rewrite hxy.
  - move=> hx; by exists x.
have hPushMeas := @pushforward_measurable_from_preimage R X E
  (@riemannian_chart_reference R m A g hg) v T.
have hRestricted : measure_measurable (measure_restrict (@euclidean_lebesgue_measure R m) A) T.
  have h := hPushMeas ltac:(by rewrite hPreimage).
  by rewrite /v riemannian_reference_pushforward in h.
have hAMeas : measure_measurable (@euclidean_lebesgue_measure R m) A.
  exact (@borel_regular_borel_measurable R E (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_borel_regular R m) A
    (open_borel_set (@riemannian_chart_domain_open R m A g hg))).
have hT := @measurable_restriction_intersection_transfer R E (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) A T hAMeas hRestricted.
have hIntersection : T `&` A=T.
  apply/seteqP; split=> x; first by move=> [hx _].
  move=> hx; split; first exact hx.
  have [y hy <-] := hx; exact: set_valP y.
by rewrite hIntersection in hT.
Qed.
