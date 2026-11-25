(** Opaque bounded-approximation interface for Federer (1969), 2.4.16, p.
    90. Source context, exact properties and the restriction-witness
    variation: BoundedMeasureApproximationUP.v. The cover and cutoff
    construction remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP CountablyMeasurableUP
  BoundedMeasureApproximationUP BoundedMeasureApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type BoundedMeasureApproximationSignature.
(** Source for [value]: an approximating sequence as in Federer
    2.4.16, p. 90, final paragraph. *)
Parameter value : forall (R : realType) (X : choiceType) (mu : set X -> \bar R), is_measure mu ->
  forall f : X -> real_norm_metric_space (scalar_absolute_value_norm R),
  is_countably_measure_measurable_function mu (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) -> nat -> X -> real_norm_metric_space (scalar_absolute_value_norm R).
(** Source for [laws]: proved approximation laws supporting the
    infinite-norm case of Federer 2.4.16, p. 90. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
  (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
  (hf : is_countably_measure_measurable_function mu (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f)), is_bounded_measure_approximation mu f (@value R X mu hm f hf).
End BoundedMeasureApproximationSignature.
Module BoundedMeasureApproximation : BoundedMeasureApproximationSignature.
(** Source for [value]: private selection from proved existence,
    supporting Federer 2.4.16, p. 90. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
  (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
  (hf : is_countably_measure_measurable_function mu (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f)) := projT1 (cid (bounded_measure_approximation_exists hm hf)).
(** Source for [laws]: verified laws of the selected sequence,
    supporting Federer 2.4.16, p. 90. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
  (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
  (hf : is_countably_measure_measurable_function mu (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f)) : is_bounded_measure_approximation mu f (value hm hf).
Proof. exact: projT2 (cid (bounded_measure_approximation_exists hm hf)). Qed.
End BoundedMeasureApproximation.
