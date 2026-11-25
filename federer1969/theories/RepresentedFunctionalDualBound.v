(** Federer (1969), 2.5.7, p. 99: the representing density has norm at most
    the closed-ball bound M, by 2.4.16, pp. 89–90. Sign-matching partial
    tests are exactly total because the represented density is total. No
    positivity of the density is assumed in these signed dual bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct PartialFunctionExtensionSealed
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureDualTestUP
  ExtendedRealBounds FunctionLatticeSeminormUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarLpFunctionalBounds TotalScalarPairing
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair TotalSignMatchingExtension
  TotalScalarTestTransfer TotalPositiveDualBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_total_unit_pairing_bound]: a total unit-ball
    test in 2.4.16 is bounded by the operator norm in Federer 2.5.7, pp.
    98–99 The inequality uses the signed integral value, bounded above by
    its absolute value. *)
Lemma represented_total_unit_pairing_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k g : X -> R) z :
  is_lp_conjugate_pair p q -> total_scalar_lp mu q k ->
  (forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k) ->
  total_scalar_lp mu p g -> total_scalar_lp_norm mu p g <= 1 ->
  is_measure_integral mu (partial_scalar_product (total_scalar_function k) (total_scalar_function g)) z ->
  z <= function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p).
Proof.
move=> hpq hk hrep hg hunit hi.
have hri := @measure_integral_graph_equivalent R X mu _ _ z (total_scalar_product_integrand_graph k g) hi.
have he : (fun x => (k x*g x)%R)=(fun x => (g x*k x)%R) by apply: funext=> x; rewrite mulrC.
rewrite he in hri.
have hgi := (@total_lp_pairing_specification_and_bound R X mu hm p q g k hpq hg hk).1.
have hz := measure_integral_unique hri hgi.
rewrite hz -(hrep g hg).
apply: le_trans (_ : (`|A g|%R)%:E <= function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p)).
- rewrite lee_fin; exact: ler_norm.
- apply: extended_real_sup_upper; exists `|A g|%R; split=> //.
  exists g; split=> //; split=> //.
  by rewrite (@total_scalar_lp_unit_ball_criterion R X mu hm p g hg).
Qed.

(** Source for [represented_finite_sign_test_bound]: the signed
    finite-exponent dual tests used for the norm identity in Federer 2.5.7,
    p. 99 Full sign matching supplies exact total-domain transfer. *)
Lemma represented_finite_sign_test_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p%:E q -> total_scalar_lp mu q k ->
  (forall f, total_scalar_lp mu p%:E f -> A f=total_scalar_pairing mu f k) ->
  forall z, sign_matching_finite_dual_values mu p (total_scalar_function k) z ->
    z <= function_operator_seminorm (total_scalar_lp mu p%:E) A (finite_total_scalar_lp_norm mu p%:E).
Proof.
move=> hpq hk hrep z [g [hg [hs hi]]].
have he := @sign_matching_total_extension_graph R X k g hs.
have [hmem hunit] := @finite_unit_test_total_transfer R X mu hm p g (PartialFunctionExtension.value g 0%R) hg he.
apply: (@represented_total_unit_pairing_bound R X mu hm p%:E q A k _ z hpq hk hrep hmem hunit).
exact: (@sign_matching_pairing_total_extension R X mu k g z hs hi).
Qed.

(** Source for [represented_infinity_sign_test_bound]: the endpoint infinity
    dual tests in the same norm identity of Federer 2.5.7, p. 99 *)
Lemma represented_infinity_sign_test_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair +oo q -> total_scalar_lp mu q k ->
  (forall f, total_scalar_lp mu +oo f -> A f=total_scalar_pairing mu f k) ->
  forall z, sign_matching_infinity_dual_values mu (total_scalar_function k) z ->
    z <= function_operator_seminorm (total_scalar_lp mu +oo) A (finite_total_scalar_lp_norm mu +oo).
Proof.
move=> hpq hk hrep z [g [hg [hs hi]]].
have he := @sign_matching_total_extension_graph R X k g hs.
have [hmem hunit] := @infinity_unit_test_total_transfer R X mu hm g (PartialFunctionExtension.value g 0%R) hg he.
apply: (@represented_total_unit_pairing_bound R X mu hm +oo q A k _ z hpq hk hrep hmem hunit).
exact: (@sign_matching_pairing_total_extension R X mu k g z hs hi).
Qed.
