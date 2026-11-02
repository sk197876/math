(** Federer (1969), 2.5.10, p. 101: the value of the geometric functional on
    a finite H^1 measurable characteristic test. This connects the
    functional's integral specification with the line measures used in the
    density contradiction. Source context: PlaneProjectionFunctional.v and
    RepresentingDensitySetBounds.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP BorelRegularMeasureUP
  TopologicalBorel HausdorffLength PlaneProjectionMeasure PlaneProjectionFunctional
  CharacteristicFunctionUP MeasureCharacteristicIntegral MeasureIntegralUniqueness
  BorelDominatedMeasureTransfer RepresentingDensitySetBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [plane_projection_characteristic_value]:
    characteristic-set evaluation of the displayed
    functional in Federer 2.5.10, p. 101.
    Every finite H^1 measurable set is allowed,
    including non-Borel sets in the completion. *)
Lemma plane_projection_characteristic_value (R : realType)
    (E : set (inner_metric_space (@euclidean_inner_productP R 2))) (s : _ -> R) :
  is_characteristic_function E s -> measure_measurable (@hausdorff_length R _) E ->
  hausdorff_length E < +oo -> (plane_projection_functional s)%:E=plane_projection_measure E.
Proof.
move=> hs hE hf.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
have hnu : measure_measurable (@plane_projection_measure R) E.
  apply: (@borel_dominated_finite_measurable R X (@hausdorff_length R X)
    (@plane_projection_measure R) (@hausdorff_length_is_measure R X)
    (plane_projection_is_measure R) (@hausdorff_length_borel_regular R X)
    _ (@plane_projection_hausdorff_bound R) E hE hf).
  move=> B hB; exact (@borel_regular_borel_measurable R X (@plane_projection_measure R)
    (plane_projection_is_measure R) (plane_projection_borel_regular R) B hB).
have hL := @finite_characteristic_total_lone R X (@hausdorff_length R X)
  (@hausdorff_length_is_measure R X) E s hs hE hf.
exact: (measure_integral_unique (plane_projection_functional_integral hL)
  (@measure_characteristic_integral R X (@plane_projection_measure R) (plane_projection_is_measure R) E s hs hnu)).
Qed.
