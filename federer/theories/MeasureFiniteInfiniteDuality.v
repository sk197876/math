(** Federer (1969), 2.4.16, p. 90: infinite input norm for finite p>1. Our
    restriction approximants give identical products against f; a positive
    full-sign mixture supplies Federer's unqualified additional sign
    restriction, which. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  CountablyMeasurableUP MeasureLpNorm MeasureDualTestUP ConjugateExponents
  BoundedMeasureApproximationUP BoundedMeasureApproximationSealed BoundedApproximationNorms
  RestrictedPowerTest FullSignUnitTest FullSignMixtureIntegral DualTestMixture ConcentratedCoefficient
  ExtendedRealBoundsUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_infinite_norm_full_sign_test_above]: the
    dual values are unbounded when phi_p(f)=infinity, Federer
    2.4.16, p. 90, final paragraph, retaining sign(u)=sign(f). *)
Lemma finite_infinite_norm_full_sign_test_above (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 < p)%R ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)=+oo ->
  forall r : R, exists z,
    sign_matching_finite_dual_values mu (finite_conjugate_exponent p) (partial_function_total f) z /\ r%:E < z.
Proof.
move=> hp hf hinf r; have hmeas := countably_measurable_function_measurable hf.
pose g := @BoundedMeasureApproximation.value R X mu hm f hf.
have hg := @BoundedMeasureApproximation.laws R X mu hm f hf.
pose s := Num.max 0%R r.
have hs0 : (0 <= s)%R by rewrite /s le_max lexx.
have hrs : (r <= s)%R by rewrite /s le_max lexx orbT.
have [n hn] := @bounded_approximation_norm_unbounded R X mu hm p f g (ltW hp) hmeas hg hinf s.
have hgn := bounded_approximation_measurable hg n.
have hfinite := @bounded_approximation_finite_lp_norm R X mu hm p f g (ltW hp) hg n.
have hnon := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu p _ hm (ltW hp) hgn.
have hfin : measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n)) \is a fin_num.
  by rewrite (ge0_fin_numE hnon).
pose a := fine (measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n))).
have hga : measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n))=a%:E.
  by rewrite /a fineK.
have hsa : (s < a)%R by move: hn; rewrite hga lte_fin.
have ha : (0 < a)%R := le_lt_trans hs0 hsa.
have [u [hu [halign hi]]] := @restricted_power_test_transfer R X mu hm p a f (g n)
  hp ha hgn hga (bounded_approximation_restriction hg n).
have [v [hv hvsg]] := @full_sign_unit_test_exists R X mu hm (finite_conjugate_exponent p) f
  (ltW (finite_conjugate_exponent_strict hp)) hf.
have [d [hd [hd1 hsd]]] := @concentrated_positive_coefficient R s a hs0 hsa.
have [hw [hwsg [z [hzi haz]]]] := @full_sign_mixture_integral R X mu hm (finite_conjugate_exponent p)
  d f u v a%:E hd hd1 hmeas hu hv halign hvsg hi.
exists z; split.
- exists (partial_function_total (dual_test_mixture d u v)); by split=> //; split.
- rewrite -EFinM in haz; apply: lt_le_trans _ haz; rewrite lte_fin.
  exact: le_lt_trans hrs hsd.
Qed.

(** Source for [finite_infinite_dual_supremum]: both infinite
    dual suprema for finite p>1 in Federer 2.4.16, p. 90,
    including the full-sign restriction. *)
Theorem finite_infinite_dual_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 < p)%R ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f) ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)=+oo ->
  is_extended_real_supremum (finite_dual_integral_values mu (finite_conjugate_exponent p) (partial_function_total f)) +oo /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu (finite_conjugate_exponent p) (partial_function_total f)) +oo.
Proof.
move=> hp hf hinf.
have hleast b : (forall z, sign_matching_finite_dual_values mu (finite_conjugate_exponent p)
    (partial_function_total f) z -> z <= b) -> +oo <= b.
  move=> hb; rewrite leNgt; apply/negP=> hbf.
  have [s [hbs _]] := @extended_rationals_order_dense R b +oo hbf.
  have [z [hz hsz]] := @finite_infinite_norm_full_sign_test_above R X mu hm p f hp hf hinf (ratr s).
  have hzb := hb z hz; by have := lt_le_trans (lt_trans hbs hsz) hzb; rewrite ltxx.
split; split; try by move=> z _; exact: leey.
- move=> b hb; apply: hleast=> z [u [hu [_ hi]]]; apply: hb; exists u; by split.
- exact hleast.
Qed.
