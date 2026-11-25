(** Federer (1969), 2.4.10, p. 85: supporting nonnegativity and monotonicity
    for the density set function. These follow before its countable covering
    inequality and need neither measurable density nor measurable test
    subsets. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP PartialExtendedOrderLoci
  MeasureSubsetIntegral MeasureDensityUP ZeroExtensionNonnegative MeasureUpperIntegralNonnegative MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_nonnegative]: nonnegative
    values of the density measure in Federer 2.4.10,
    p. 85, without assuming density measurability. *)
Lemma measure_density_nonnegative (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (g : partial_function X (extended_real_line R)) :
  is_measure_density mu g nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus g) ->
  forall A, 0 <= nu A.
Proof.
move=> hn hp A; rewrite (hn A); apply: (@measure_upper_integral_nonnegative R X mu hm).
exact (@zero_extension_nonnegative_almost R X mu hm A g hp).
Qed.

(** Source for [measure_density_monotone]: supporting subset
    monotonicity for the density measure of Federer 2.4.10,
    p. 85, derived directly from upper-integral monotonicity. *)
Lemma measure_density_monotone (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (g : partial_function X (extended_real_line R)) (A B : set X) :
  is_measure_density mu g nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus g) ->
  A `<=` B -> nu A <= nu B.
Proof.
move=> hn hp hAB; rewrite (hn A) (hn B); apply: (@measure_upper_integral_monotone R X mu hm).
exact (@nonnegative_zero_extension_subset_order R X mu hm A B g hAB hp).
Qed.
