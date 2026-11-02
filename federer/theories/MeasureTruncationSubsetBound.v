(** Federer (1969), 2.4.11, proof p. 86: integral over A is bounded by the
    whole truncation-tail integral plus n times the measure of A. Source
    editions: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialUpperTruncation PartialExtendedArithmetic PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralAddition MeasureIntegralComparison
  MeasureFiniteCharacteristicIntegral MeasureSummableFiniteValues MeasureSubsetIntegral
  MeasureNonnegativeSubsetBound TruncationSubsetComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_truncation_subset_bound]: the main
    estimate in Federer 2.4.11, proof p. 86,
    before choosing delta. The bound allows infinite measures
    of A; the final theorem imposes a finite small bound. *)
Lemma measure_truncation_subset_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (A : set X) (b t c : R) :
  is_measure_integral mu f b%:E -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_measurable mu A -> (0 < c)%R -> (0 <= t)%R ->
  is_measure_integral mu (partial_extended_function_subtract f (partial_upper_truncation f c%:E)) t%:E ->
  exists a : R, is_measure_subset_integral mu A f a%:E /\ a%:E <= t%:E+c%:E*mu A.
Proof.
move=> hf hp hA hc ht htail.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have hi := @measure_positive_characteristic_integral R X mu hm A s c hs hA hc.
have hadd : extended_add t%:E (c%:E*mu A)=Some (t%:E+c%:E*mu A).
  by rewrite /extended_add fin_num_adde_defr.
have hsum := @measure_integral_add R X mu hm _ _ t%:E (c%:E*mu A) _ htail hi hadd.
have [hcut [hcut0 hcutb]] := @nonnegative_zero_extension_integral_bound R X mu hm A f b%:E hA hf hp.
pose v := measure_lower_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f).
have hvfin : v \is a fin_num.
  rewrite (ge0_fin_numE hcut0); exact: le_lt_trans hcutb (ltry b).
exists (fine v); split; first by rewrite fineK.
rewrite fineK //; apply: (@measure_integral_monotone R X mu hm _ _ v _ hcut hsum).
have hfs : is_measure_summable mu f by exists b.
have hff := @measure_summable_finite_almost R X mu hm f hfs.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hff)=> x [y [hy hyfin]].
have hy' : partial_function_graph f x (fine y)%:E by rewrite fineK.
exact (@truncation_subset_pointwise_bound R X f A s c (fine y) x hs (ltW hc) hy').
Qed.
