(** Federer (1969), 2.5.10, p. 101: vertical segments contribute zero to the
    projected-counting functional. This supporting consequence of 2.10.10,
    p. 176, says that a Borel set with null projection has zero
    projected-counting measure. Multiplicity may be infinite on that null
    image. Source context: PlaneProjectionMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralUniqueness MeasureConullZeroIntegral LebesgueScalarMeasure TopologicalBorel
  MappingMultiplicity MappingMultiplicityLaws PlaneProjectionMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [plane_projection_null_image]: supporting
    zero-measure assertion for the vertical tests in
    Federer 2.5.10, p. 101, from the actual
    multiplicity formula of 2.10.10, p. 176.
    Infinite counts on a null set cause no exception. *)
Lemma plane_projection_null_image (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  borel_set A -> lebesgue_scalar_measure ((@plane_first_projection R) @` A)=0 ->
  plane_projection_measure A=0.
Proof.
move=> hA hz.
have hi := @plane_projection_multiplicity_integral R A hA.
have ha : measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set y | @mapping_multiplicity R _ R (@plane_first_projection R) A y=0].
  apply: (@measure_null_subset R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    _ ((@plane_first_projection R) @` A) _ hz).
  move=> y hny; apply: contrapT=> hn; apply: hny.
  exact: (@mapping_multiplicity_zero_iff R _ R (@plane_first_projection R) A y).2 hn.
apply: (measure_integral_unique hi).
exact (@measure_almost_zero_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (partial_function_total
    (fun y => (@mapping_multiplicity R _ R (@plane_first_projection R) A y : extended_real_line R))) ha).
Qed.
