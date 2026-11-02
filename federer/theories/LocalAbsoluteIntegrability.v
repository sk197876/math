(** The local absolute-integrability hypothesis of Federer (1969), 2.9.8, p.
    156. The printed scalar range is the extended real line. Finite
    integrals of the absolute value on bounded measurable sets imply finite
    subset integrals of both parts and of the signed function. The
    supporting comparisons use the proved integral laws 2.4.4, pp. 82–83,
    and retain actual partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP
  PartialFunctionPostcomposition PartialZeroExtension PartialZeroExtensionLaws
  PartialExtendedOrderLoci PartialAbsolutePartsGraph PartialFunctionIntegralParts
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableExtendedParts
  MeasurableZeroExtension ZeroExtensionNonnegative CoveringFamilyUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralPartsDifference MeasureSubsetIntegral
  MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_locally_absolutely_integrable]: direct
    hypothesis of Federer 2.9.8, p. 156:
    the absolute-value integral is finite on every
    bounded phi measurable set. Finite integral
    witnesses express both existence and value. *)
Definition is_locally_absolutely_integrable (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :=
  forall A, metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A (partial_extended_function_absolute_value f) a%:E.

(** Source for [finite_absolute_subset_dominates]: supporting
    finite part-integral bound for Federer 2.9.8,
    p. 156. Any measurable nonnegative transform
    bounded by the absolute value has finite
    integral on the same target. The transform's
    laws and measurability are explicit assumptions. *)
Lemma finite_absolute_subset_dominates (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (q : extended_real_line R -> extended_real_line R) A (a : R) :
  is_measure phi -> is_measure_measurable_function phi f ->
  is_measure_measurable_function phi (partial_function_postcompose f q) ->
  (forall y, 0<=q y /\ q y<=`|y|) -> measure_measurable phi A ->
  is_measure_subset_integral phi A (partial_extended_function_absolute_value f) a%:E ->
  exists b : R, is_measure_subset_integral phi A (partial_function_postcompose f q) b%:E.
Proof.
move=> hm hf hqmeas hq hA habs.
pose g := partial_function_postcompose f q.
pose G := partial_function_zero_extension (0 : extended_real_line R) A g.
pose H := partial_function_zero_extension (0 : extended_real_line R) A (partial_extended_function_absolute_value f).
have hp : measure_almost_everywhere phi (partial_extended_nonnegative_locus g).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hf))=> x [y hy].
  exists (q y); split; [by exists y; split|exact: (hq y).1].
have hGm := @measurable_zero_extension R X (extended_real_line R) phi hm 0 A g hA hqmeas.
have hGp := @zero_extension_nonnegative_almost R X phi hm A g hp.
have [hGi hG0] := @nonnegative_measurable_function_integral R X phi hm G hGm hGp.
have horder : measure_almost_everywhere phi (partial_extended_le_locus G H).
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ (measurable_function_domain hf))=> x [y hy].
  case: (pselect (A x))=> hx.
  - exists (q y),`|y|; split.
    + apply/partial_function_zero_extension_graph; left; split=> //; exists y; by split.
    + split; last exact: (hq y).2.
      apply/partial_function_zero_extension_graph; left; split=> //; exists y; by split.
  - exists 0,0; split.
    + apply/partial_function_zero_extension_graph; right; by split.
    + split; last exact: lexx.
      apply/partial_function_zero_extension_graph; right; by split.
have hbound := @measure_integral_monotone R X phi hm G H _ a%:E hGi habs horder.
have hfin : measure_lower_integral phi G \is a fin_num.
  rewrite (ge0_fin_numE hG0); exact: le_lt_trans hbound (ltry _).
exists (fine (measure_lower_integral phi G)); rewrite fineK //; exact hGi.
Qed.

(** Source for [locally_absolutely_integrable_parts]: supporting two
    nonnegative applications in the signed case of Federer 2.9.8, p. 156
    Positive and negative parts have finite local subset integrals under the
    original bounded measurable hypothesis. *)
Lemma locally_absolutely_integrable_parts (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_measure phi -> is_measure_measurable_function phi f -> is_locally_absolutely_integrable phi f ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists p : R,
    is_measure_subset_integral phi A (partial_extended_function_positive_part f) p%:E) /\
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists n : R,
    is_measure_subset_integral phi A (partial_extended_function_negative_part f) n%:E).
Proof.
move=> hm hf hlocal; split=> A hAb hAm; have [a ha] := hlocal A hAb hAm.
- apply: (@finite_absolute_subset_dominates R X phi f (fun y => extended_positive_part y) A a hm hf
    (@measurable_extended_positive_part R X phi hm f hf) _ hAm ha)=> y.
  split; first exact: extended_positive_part_nonnegative.
  by rewrite /extended_positive_part ge_max lee_abs abse_ge0.
- apply: (@finite_absolute_subset_dominates R X phi f (fun y => extended_negative_part y) A a hm hf
    (@measurable_extended_negative_part R X phi hm f hf) _ hAm ha)=> y.
  split; first exact: extended_negative_part_nonnegative.
  rewrite /extended_negative_part /extended_positive_part ge_max abse_ge0 andbT.
  by rewrite -[in leRHS]abseN lee_abs.
Qed.

(** Source for [locally_absolutely_integrable_part_values]:
    supporting signed subset integral in Federer 2.9.8,
    p. 156. The integral equals the
    difference of the two finite part integrals,
    using 2.4.4(6), p. 83. Zero
    extension commutes with both part operations. *)
Lemma locally_absolutely_integrable_part_values (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_measure phi -> is_measure_measurable_function phi f -> is_locally_absolutely_integrable phi f ->
  forall A, metric_set_bounded A -> measure_measurable phi A -> exists p n : R,
    is_measure_subset_integral phi A (partial_extended_function_positive_part f) p%:E /\
    is_measure_subset_integral phi A (partial_extended_function_negative_part f) n%:E /\
    is_measure_subset_integral phi A f (p-n)%R%:E.
Proof.
move=> hm hf hlocal A hAb hAm.
have [hpos hneg] := @locally_absolutely_integrable_parts R X phi f hm hf hlocal.
have [p hp] := hpos A hAb hAm; have [n hn] := hneg A hAb hAm.
pose F := partial_function_zero_extension (0 : extended_real_line R) A f.
have hP : is_measure_integral phi (partial_extended_function_positive_part F) p%:E.
  apply: (@measure_integral_graph_equivalent R X phi _ _ p%:E _ hp)=> x z.
  symmetry; apply: (@partial_zero_extension_postcompose X (extended_real_line R) (extended_real_line R)
    0 0 A f (fun y => extended_positive_part y) x z).
  by rewrite /extended_positive_part maxxx.
have hN : is_measure_integral phi (partial_extended_function_negative_part F) n%:E.
  apply: (@measure_integral_graph_equivalent R X phi _ _ n%:E _ hn)=> x z.
  symmetry; apply: (@partial_zero_extension_postcompose X (extended_real_line R) (extended_real_line R)
    0 0 A f (fun y => extended_negative_part y) x z).
  by rewrite /extended_negative_part oppe0 /extended_positive_part maxxx.
have hsub : extended_subtract p%:E n%:E=Some (p-n)%R%:E by rewrite /extended_subtract /extended_add /=.
exists p,n; split=> //; split=> //.
exact (@measure_integral_from_parts R X phi hm F p%:E n%:E (p-n)%R%:E hP hN hsub).
Qed.
