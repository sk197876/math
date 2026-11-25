(** Federer (1969), 2.4.4(3), p. 82, with
    2.4.10, p. 85: positive finite scalars commute
    with the actual subset integral. This supports both
    frozen determinant factors in 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  PartialFunctionPostcomposition MeasurableExtendedScale MeasureUP MeasureIntegralUP
  MeasureUpperIntegralScale MeasureSubsetIntegral MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_subset_integral_positive_scale]:
    positive-scalar case of 2.4.4(3), p. 82,
    for genuine subset integrals, supporting 3.2.46,
    p. 282. Proper partial domains, zero densities
    and infinite signed integral values are retained. *)
Lemma measure_subset_integral_positive_scale (R : realType) (X : choiceType)
    (mu : classical_sets.set X -> \bar R) (S : classical_sets.set X)
    (u : partial_function X (extended_real_line R)) (c : R) a :
  is_measure mu -> (0<c)%R -> is_measure_subset_integral mu S u a ->
  is_measure_subset_integral mu S (partial_extended_function_scale c u) (c%:E*a).
Proof.
move=> hMu hc hIntegral.
have hScaled := @measure_integral_positive_scale R X mu hMu c
  (partial_function_zero_extension (0 : extended_real_line R) S u) a hc hIntegral.
apply:(measure_integral_graph_equivalent _ hScaled)=> x z.
exact (@partial_zero_extension_postcompose X (extended_real_line R) (extended_real_line R)
  0 0 S u (fun v=>(c%:E*v : extended_real_line R)) x z (mule0 _)).
Qed.
