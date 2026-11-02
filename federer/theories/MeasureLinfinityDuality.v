(** Federer (1969), 2.4.16, pp. 89–90: p=infinity, q=1, including zero and
    infinite essential norm. The test ball follows the erratum, p. 2, book
    p. 89 line 19. The proofs below retain Federer's unqualified pointwise
    sign clause. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasurableFunctionUP CountablyMeasurableUP MeasureIntegralUP
  MeasureEssentialNorm MeasureDualTestUP CharacteristicFunctionSealed CharacteristicDualTest
  EssentialNormPositiveSubset FullSignUnitTest FullSignMixtureIntegral DualTestMixture
  ConcentratedCoefficient SignMatchingIntegral MeasureLinfinityDualUpperBound
  ExtendedRealBoundsUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linfinity_full_sign_test_above]: the positive
    first coefficient can make the integral arbitrarily close from
    below to phi_infinity(f), Federer 2.4.16, p. 90. The
    essential norm may be infinite. *)
Lemma linfinity_full_sign_test_above (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (r t : R) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  (0 <= r)%R -> (r < t)%R ->
  t%:E < measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f) ->
  exists z, sign_matching_finite_dual_values mu 1%R (partial_function_total f) z /\ r%:E < z.
Proof.
move=> hf hr hrt htn; have ht : (0 < t)%R := le_lt_trans hr hrt.
have hmeas := countably_measurable_function_measurable hf.
have [A [hA [hAp [hAf hAt]]]] := @essential_norm_positive_finite_superlevel_subset R X mu hm f t hf ht htn.
have hAfin : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
pose b := fine (mu A).
have hAb : mu A=b%:E by rewrite /b fineK.
have hb : (0 < b)%R by move: hAp; rewrite hAb lte_fin.
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
have [hu [z [hzi htz]]] := @characteristic_dual_test_admissible R X mu hm A s b t f
  hs hA hAb hb ht hmeas hAt.
have hup := @characteristic_dual_test_bounds R X A s b t f hs hb ht hAt.
have [v [hv hvsign]] := @full_sign_unit_test_exists R X mu hm 1%R f (lexx _) hf.
have [d [hd [hd1 hdr]]] := @concentrated_positive_coefficient R r t hr hrt.
have [hw [hwsg [a [hai hza]]]] := @full_sign_mixture_integral R X mu hm 1%R d f
  (characteristic_dual_test b s f) v z hd hd1 hmeas hu hv (fun x => (hup x).2.1) hvsign hzi.
exists a; split.
- exists (partial_function_total (dual_test_mixture d (characteristic_dual_test b s f) v)).
  by split=> //; split.
- have h1d : 0 <= (((1-d)%R)%:E : \bar R) by rewrite lee_fin subr_ge0; exact: ltW hd1.
  have hh := lee_wpmul2l h1d htz.
  rewrite -EFinM in hh.
  apply: lt_le_trans _ (le_trans hh hza); by rewrite lte_fin.
Qed.

(** Source for [linfinity_dual_supremum]: both supremum assertions
    of Federer 2.4.16 for p=infinity and q=1, pp. 89–90.
    Countably measurable total functions are exactly the printed domain;
    all three essential-norm cases and the full-sign restriction are included. *)
Theorem linfinity_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  is_extended_real_supremum (finite_dual_integral_values mu 1%R (partial_function_total f))
    (measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f)) /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu 1%R (partial_function_total f))
    (measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f)).
Proof.
move=> hf; have hmeas := countably_measurable_function_measurable hf.
have hupper := @linfinity_dual_integral_upper_bound R X mu hm _ hmeas.
have [v [hv hvsg]] := @full_sign_unit_test_exists R X mu hm 1%R f (lexx _) hf.
have [z0 [hi0 hz0]] := @sign_matching_total_integral_nonnegative R X mu hm f v hmeas hv.1.2.1.1 hvsg.
have hz0mem : sign_matching_finite_dual_values mu 1%R (partial_function_total f) z0.
  exists (partial_function_total v); by split=> //; split.
have hleast b : (forall z, sign_matching_finite_dual_values mu 1%R (partial_function_total f) z -> z <= b) ->
    measure_essential_norm mu (fun y : R => `|y|%R) (partial_function_total f) <= b.
  move=> hb; have hb0 : 0 <= b := le_trans hz0 (hb z0 hz0mem).
  rewrite leNgt; apply/negP=> hbn.
  have [s [hbs hsn]] := @extended_rationals_order_dense R b _ hbn.
  have [t [hst htn]] := @extended_rationals_order_dense R ((ratr s : R))%:E _ hsn.
  have hs0 : (0 <= (ratr s : R))%R by have hh := le_trans hb0 (ltW hbs); move: hh; rewrite lee_fin.
  have hstR : ((ratr s : R) < (ratr t : R))%R by move: hst; rewrite lte_fin.
  have [z [hz hsz]] := @linfinity_full_sign_test_above R X mu hm f ((ratr s : R)) ((ratr t : R)) hf hs0 hstR htn.
  have hzb := hb z hz; by have := lt_le_trans (lt_trans hbs hsz) hzb; rewrite ltxx.
split; split.
- exact hupper.
- move=> b hb; apply: hleast=> z [u [hu [_ hi]]]; apply: hb; exists u; by split.
- move=> z [u [hu [_ hi]]]; apply: hupper; exists u; by split.
- exact hleast.
Qed.
