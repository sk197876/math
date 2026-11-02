(** The projection-cover estimate for Federer (1969), 2.5.10, p. 101. It
    combines 2.10.7, p. 175, and the cost comparison of 2.10.11, p. 176:
    Lebesgue measure of a nonexpanding real image is at most the original
    diameter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter MetricDiameterMaps
  MeasureUP MeasureBasic LebesgueScalarMeasure LebesgueDiameterBound
  BorelImageCoverCost BorelCaratheodoryMeasure BorelCostHausdorffBound HausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonexpanding_real_image_diameter_bound]:
    the diameter-cost estimate for the projection in
    Federer 2.5.10, p. 101, using 2.10.7,
    p. 175, and 2.10.11, p. 176.
    Empty and unbounded sets are included. *)
Lemma nonexpanding_real_image_diameter_bound (R : realType) (X : metricType R)
    (f : X -> real_line_metric R) :
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  forall A, lebesgue_scalar_measure (f @` A)<=extended_metric_diameter A.
Proof.
move=> hf A; case: (pselect (A !=set0))=> [hA|hn].
- have hi : f @` A !=set0.
    have [x hx] := hA; exists (f x); by exists x.
  apply: le_trans (lebesgue_scalar_diameter_bound hi) _.
  exact (@extended_metric_diameter_nonexpanding R X [the metricType R of real_line_metric R] f hf A).
- have he : A=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hn; by exists x.
  rewrite he image_set0 (measure_empty (lebesgue_scalar_is_measure R)).
  exact (@metric_diameter_nonnegative R X set0 _ (extended_metric_diameter_specification set0)).
Qed.

(** Source for [real_projection_caratheodory_bound]: the
    measure domination underlying the integral bound in
    Federer 2.5.10, p. 101, by the
    Caratheodory construction of 2.10.10–11, p. 176.
    The fibre-counting formula is a separate theorem. *)
Theorem real_projection_caratheodory_bound (R : realType) (X : metricType R)
    (f : X -> real_line_metric R) :
  (forall x y, (mdist (f x) (f y)<=mdist x y)%R) ->
  forall A, borel_caratheodory_measure (borel_image_cover_cost f (@lebesgue_scalar_measure R)) A
    <=hausdorff_length A.
Proof.
move=> hf; apply: borel_cost_hausdorff_length_bound.
- exact (@borel_image_cover_cost_laws R X R f (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)).
- move=> A hA; exact (@nonexpanding_real_image_diameter_bound R X f hf A).
Qed.
