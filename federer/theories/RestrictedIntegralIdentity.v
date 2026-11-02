(** Federer (1969), 2.5.10, p. 101: the local integral for phi restricted to
    A equals the subset integral defined by zero extension in 2.4.10, p. 85.
    The upper identity has been proved from the step definitions; negation
    gives the lower identity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralNegation MeasureBoundGraphEquivalence MeasureIntegralSqueeze
  RestrictedFunctionMeasurability RestrictedMeasurabilityConverse RestrictedUpperIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_lower_integral_zero_extension]:
    supporting lower-integral identity for Federer 2.5.10, p. 101,
    by the negation law 2.4.3(1), p. 81. *)
Lemma restricted_lower_integral_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) :
  measure_measurable mu B ->
  measure_lower_integral (measure_restrict mu B) f=
    measure_lower_integral mu (partial_function_zero_extension (0 : extended_real_line R) B f).
Proof.
move=> hB.
rewrite (@measure_lower_integral_negation R X (measure_restrict mu B) (measure_restrict_is_measure hm B))
  (@measure_lower_integral_negation R X mu hm)
  (@restricted_upper_integral_zero_extension R X mu hm B _ hB).
congr (- _).
symmetry; apply: measure_upper_integral_graph_equivalent=> x z.
exact: (@partial_zero_extension_postcompose X (extended_real_line R) (extended_real_line R)
  0 0 B f (fun z => -z) x z (oppe0)).
Qed.

(** Source for [restricted_integral_zero_extension_iff]: actual
    integral equivalence used in Federer 2.5.10, p. 101,
    with restriction from 2.1.2, p. 54, and subset integral
    from 2.4.10, p. 85. Both definedness and value are preserved,
    including signed infinite values and exact partial domains. *)
Theorem restricted_integral_zero_extension_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X)
    (f : partial_function X (extended_real_line R)) a :
  measure_measurable mu B ->
  (is_measure_integral (measure_restrict mu B) f a <->
   is_measure_integral mu (partial_function_zero_extension (0 : extended_real_line R) B f) a).
Proof.
move=> hB.
have hu := @restricted_upper_integral_zero_extension R X mu hm B f hB.
have hl := @restricted_lower_integral_zero_extension R X mu hm B f hB.
split=> hi.
- have hmz := @restricted_measurable_zero_extension R X (extended_real_line R) mu hm 0 B f hB hi.1.
  apply: (@measure_integral_squeeze R X mu hm _ a hmz).
  + rewrite -hu; have he := measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
    by rewrite he.
  + rewrite -hl; have he := measure_lower_integral_unique (measure_lower_integral_specification _ _) hi.2.2.
    by rewrite he.
- have hmf := @zero_extension_measurable_for_restriction R X (extended_real_line R) mu hm 0 B f hi.1.
  apply: (@measure_integral_squeeze R X (measure_restrict mu B) (measure_restrict_is_measure hm B) f a hmf).
  + rewrite hu; have he := measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
    by rewrite he.
  + rewrite hl; have he := measure_lower_integral_unique (measure_lower_integral_specification _ _) hi.2.2.
    by rewrite he.
Qed.
