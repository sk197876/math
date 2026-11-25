(** Opaque positive-weight interface supporting Federer (1969), 2.4.16, p.
    90. Source context and exact pointwise and integral laws:
    PositiveIntegrableWeightUP.v. The cover, coefficients and series
    construction remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP CountablyMeasurableUP
  PositiveIntegrableWeightUP PositiveIntegrableWeightConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type PositiveIntegrableWeightSignature.
(** Source for [value]: an integrable positive weight on the
    prescribed locus, supporting Federer 2.4.16, p. 90. *)
Parameter value : forall (R : realType) (X : choiceType)
  (mu : set X -> \bar R), is_measure mu -> forall A,
  measure_countably_measurable mu A -> X -> real_norm_metric_space (scalar_absolute_value_norm R).
(** Source for [laws]: the proved weight bounds and exact support,
    supporting the sign constraint in Federer 2.4.16, p. 90. *)
Parameter laws : forall (R : realType) (X : choiceType)
  (mu : set X -> \bar R) (hm : is_measure mu) A (hA : measure_countably_measurable mu A),
  is_positive_integrable_weight mu A (@value R X mu hm A hA).
End PositiveIntegrableWeightSignature.

Module PositiveIntegrableWeight : PositiveIntegrableWeightSignature.
(** Source for [value]: private choice from proved existence,
    supporting Federer 2.4.16, p. 90. *)
Definition value (R : realType) (X : choiceType)
  (mu : set X -> \bar R) (hm : is_measure mu) A (hA : measure_countably_measurable mu A) :=
  projT1 (cid (positive_integrable_weight_exists hm hA)).
(** Source for [laws]: verified laws of the selected witness,
    supporting Federer 2.4.16, p. 90. *)
Lemma laws (R : realType) (X : choiceType)
  (mu : set X -> \bar R) (hm : is_measure mu) A (hA : measure_countably_measurable mu A) :
  is_positive_integrable_weight mu A (value hm hA).
Proof. exact: projT2 (cid (positive_integrable_weight_exists hm hA)). Qed.
End PositiveIntegrableWeight.
