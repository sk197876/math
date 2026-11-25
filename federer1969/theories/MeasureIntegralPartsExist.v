(** Federer (1969), proof of 2.4.4(6), p. 83: both parts of a measurable
    function are integrable because they are nonnegative and measurable.
    Their integrals may both be infinite, in which case their difference is
    undefined. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableExtendedParts
  PartialExtendedOrderLoci PartialFunctionIntegralParts MeasureUpperIntegralPositivePart
  MeasureIntegralUP MeasureNonnegativeIntegral MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_parts_nonnegative_almost]: supporting
    nonnegative-value assertion for f+ and f- in Federer
    2.4.4(6), proof p. 83, using the original conull domain. *)
Lemma partial_parts_nonnegative_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_extended_function_positive_part f)) /\
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_extended_function_negative_part f)).
Proof.
move=> hd; split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists (extended_positive_part y); split; first by exists y; split.
  exact: extended_positive_part_nonnegative.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists (extended_negative_part y); split; first by exists y; split.
  exact: extended_negative_part_nonnegative.
Qed.

(** Source for [measurable_function_parts_integrals]: supporting
    existence and nonnegativity of the two part integrals in
    Federer 2.4.4(6), proof p. 83. This does not
    assert that their difference is defined. *)
Lemma measurable_function_parts_integrals (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> exists P N,
  is_measure_integral mu (partial_extended_function_positive_part f) P /\
  is_measure_integral mu (partial_extended_function_negative_part f) N /\ 0 <= P /\ 0 <= N.
Proof.
move=> hf; have [hp hn] := @partial_parts_nonnegative_almost R X mu hm f (measurable_function_domain hf).
have hpm := @measurable_extended_positive_part R X mu hm f hf.
have hnm := @measurable_extended_negative_part R X mu hm f hf.
have [hpi hp0] := @nonnegative_measurable_function_integral R X mu hm _ hpm hp.
have [hni hn0] := @nonnegative_measurable_function_integral R X mu hm _ hnm hn.
exists (measure_lower_integral mu (partial_extended_function_positive_part f)),
  (measure_lower_integral mu (partial_extended_function_negative_part f)).
by split=> //; split=> //; split.
Qed.
