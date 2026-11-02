(** Federer (1969), 2.5.7, pp. 98–99: integration of products of total
    scalar functions in conjugate Lebesgue spaces. The finite-exponent bound
    is 2.4.14, p. 88; the endpoint follows from the essential bound in
    2.4.12, p. 86, and integral comparison 2.4.4(5), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower RealPower
  PartialScalarProduct PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralComparison
  MeasureIntegralAbsolute MeasureAbsoluteSummability MeasureFiniteRealScaleIntegral MeasureLoneNormIntegral
  MeasureEssentialNormAttainment MeasureHolderScalar SummableRealFunctionUP TotalScalarLpUP
  TotalScalarLpFiniteSeminorm TotalScalarLpNormLaws TotalScalarPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_pairing_finite_exponents]: summability and
    Holder bound for the finite-exponent pairing used in Federer 2.5.7, pp.
    98–99, by 2.4.14, p. 88 Zero norms are included. *)
Theorem total_scalar_pairing_finite_exponents (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R) (f g : X -> R) :
  (p^-1+q^-1 = 1)%R -> total_scalar_lp mu p%:E f -> total_scalar_lp mu q%:E g ->
  exists c : R, is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) c%:E /\
    (`|c| <= finite_total_scalar_lp_norm mu p%:E f*finite_total_scalar_lp_norm mu q%:E g)%R.
Proof.
move=> hpq hf hg.
have [c [hi hb]] := @measure_holder_scalar_finite R X mu hm p q
  (finite_total_scalar_lp_norm mu p%:E f) (finite_total_scalar_lp_norm mu q%:E g)
  (total_scalar_function f) (total_scalar_function g) hf.1 hg.1 hpq hf.2.1 hg.2.1
  (esym (@finite_total_scalar_lp_norm_exact R X mu hm p%:E f hf))
  (esym (@finite_total_scalar_lp_norm_exact R X mu hm q%:E g hg)).
exists c; split=> //.
exact: (@measure_integral_graph_equivalent R X mu _ _ _ (total_scalar_product_integrand_graph f g) hi).
Qed.
