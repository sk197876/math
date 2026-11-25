(** Federer (1969), 2.9.25, p. 169: represent the integral of the absolute
    density on measurable sets by the measure of 2.4.10, p. 85. These are
    consequences of the existing abstract integral and sealed density laws,
    not additional axioms. No relevant local erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureDensityUP MeasureDensity
  MeasureDensityNullSets SummableSubsetRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_density_measurable_mass]: supporting
    identification of the actual finite subset integral with
    the prescribed density mass in Federer 2.9.25, p. 169,
    using 2.4.10, p. 85. Summability supplies existence;
    uniqueness identifies its value with the upper integral. *)
Lemma summable_density_measurable_mass (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (A : set X) :
  is_measure_summable mu f -> measure_measurable mu A ->
  is_measure_subset_integral mu A f (measure_with_density mu f A).
Proof.
move=> hf hA.
have [a ha] := @summable_measurable_zero_extension R X mu hm A f hA hf.
have he := @measure_upper_integral_unique R X mu _ _ a%:E
  (measure_upper_integral_specification mu _) ha.2.1.
by rewrite (measure_with_density_laws mu f A) /measure_subset_upper_integral he.
Qed.

(** Source for [absolute_density_is_measure]: supporting
    positive measure for the increment sums in Federer 2.9.25,
    p. 169, by 2.4.10, p. 85. The density is the
    exact partial absolute value; its domain is conull by
    measurability, rather than by assigning exceptional values. *)
Lemma absolute_density_is_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure (measure_with_density mu (partial_extended_function_absolute_value f)).
Proof.
move=> hf; apply: (@measure_with_density_is_measure R X mu hm
  (partial_extended_function_absolute_value f)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf))=> x [z hz].
exists `|z|; split; first by exists z; split.
exact: abse_ge0.
Qed.

(** Source for [absolute_density_measurable]: supporting
    preservation of measurable sets in the density-measure
    proof of Federer 2.9.25, p. 169, by 2.4.10, p. 85. *)
Lemma absolute_density_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (A : set X) :
  is_measure_measurable_function mu f -> measure_measurable mu A ->
  measure_measurable (measure_with_density mu (partial_extended_function_absolute_value f)) A.
Proof.
move=> hf hA; apply: (@measure_with_density_measurable R X mu hm
  (partial_extended_function_absolute_value f) A _ hA).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf))=> x [z hz].
exists `|z|; split; first by exists z; split.
exact: abse_ge0.
Qed.
