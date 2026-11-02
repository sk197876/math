(** Federer (1969), 2.5.7, pp. 98–99: integration of products of total
    scalar functions in conjugate Lebesgue spaces. The finite-exponent bound
    is 2.4.14, p. 88; the endpoint follows from the essential bound in
    2.4.12, p. 86, and integral comparison 2.4.4(5), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower RealPower
  PartialScalarProduct PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralComparison
  MeasureIntegralAbsolute MeasureAbsoluteSummability MeasureFiniteRealScaleIntegral MeasureLoneNormIntegral
  MeasureEssentialNormAttainment SummableRealFunctionUP TotalScalarLpUP
  TotalScalarLpFiniteSeminorm TotalScalarLpNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_product_integrand_graph]: supporting
    identification of the product integrand in Federer 2.5.7, pp. 98–99 Both
    factors are total and finite-valued. *)
Lemma total_scalar_product_integrand_graph (R : realType) (X : Type) (f g : X -> R) x z :
  partial_function_graph (partial_scalar_product (total_scalar_function f) (total_scalar_function g)) x z <->
  partial_function_graph (real_total_integrand (fun x => (f x*g x)%R)) x z.
Proof.
rewrite partial_scalar_product_graph real_total_integrand_graph; split.
- move=> [a [b [ha [hb he]]]].
  by rewrite (ha : f x=a) (hb : g x=b).
- move=> he; exists (f x),(g x); by split=> //; split.
Qed.

(** Source for [total_scalar_lone_absolute_integral]: the integral of |f|
    equals phi_(1)(f), from Federer 2.4.12, p. 86, used for endpoint
    pairings in 2.5.7, pp. 98–99 *)
Lemma total_scalar_lone_absolute_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  total_scalar_lp mu 1 f ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x|%R))
    (finite_total_scalar_lp_norm mu 1 f)%:E.
Proof.
move=> hf.
have hlp := (@total_scalar_lp_finite_equivalence R X mu hm 1%R f).1 hf.
have hi := @measure_lone_norm_integral R X R^o (fun y : R => `|y|%R)
  (scalar_absolute_value_norm R) mu hm (total_scalar_function f) hlp.
rewrite (@finite_total_scalar_lp_norm_exact R X mu hm 1 f hf).
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
rewrite real_total_integrand_graph; split.
- move=> [y [hy he]].
  by rewrite -(hy : f x=y) real_power_one_exponent ?normr_ge0 in he.
- move=> he; exists (f x); split=> //.
  by rewrite real_power_one_exponent ?normr_ge0.
Qed.

(** Source for [total_scalar_pairing_bounded_factor]: endpoint Holder
    estimate supporting Federer 2.5.7, pp. 98–99 The bound on the second
    factor holds almost everywhere and may be zero. *)
Theorem total_scalar_pairing_bounded_factor (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (b : R) :
  total_scalar_lp mu 1 f -> is_measure_measurable_function mu (total_scalar_function g) ->
  (0 <= b)%R -> measure_almost_everywhere mu [set x | (`|g x| <= b)%R] ->
  exists c : R, is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) c%:E /\
    (`|c| <= b*finite_total_scalar_lp_norm mu 1 f)%R.
Proof.
move=> hf hg hb hbg.
pose F := real_total_integrand (fun x => (f x*g x)%R).
pose H := real_total_integrand (fun x => (b*`|f x|)%R).
have hfi := @total_scalar_lone_absolute_integral R X mu hm f hf.
have hhi : is_measure_integral mu H (b*finite_total_scalar_lp_norm mu 1 f)%:E.
  exact: (@measure_finite_real_total_scale_integral R X mu hm
    (fun x => `|f x|%R) (finite_total_scalar_lp_norm mu 1 f) b hfi).
have hF : is_measure_measurable_function mu F.
  have hmprod := @measurable_scalar_product R X mu hm
    (total_scalar_function f) (total_scalar_function g) hf.2.1 hg.
  exact: (@measurable_function_graph_equivalent R X _ mu _ F
    (total_scalar_product_integrand_graph f g) hmprod).
have hdom : measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_absolute_value F) H).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hbg)=> x hx.
  exists (`|f x*g x|%R)%:E,(b*`|f x|)%:E; split.
  - exists (f x*g x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first by apply/real_total_integrand_graph.
    rewrite lee_fin normrM [(b*_)%R]mulrC.
    apply: (ler_wpM2l (normr_ge0 (f x))); exact: hx.
have [[c hci] _] := @measure_dominated_summable R X mu hm F H hF
  (ex_intro _ (b*finite_total_scalar_lp_norm mu 1 f)%R hhi) hdom.
have [d [hdi hcd]] := @measure_integral_absolute_bound R X mu hm F c%:E hci.
have hdb := @measure_integral_monotone R X mu hm _ H d _ hdi hhi hdom.
exists c; split=> //.
have hh := le_trans hcd hdb; by rewrite abse_EFin lee_fin in hh.
Qed.

(** Source for [total_scalar_pairing_lone_linfinity]: the full p=1,
    q=infinity Holder bound used in Federer 2.5.7, pp. 98–99 No assumption
    that the whole space has finite measure is made. *)
Theorem total_scalar_pairing_lone_linfinity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  total_scalar_lp mu 1 f -> total_scalar_lp mu +oo g ->
  exists c : R, is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) c%:E /\
    (`|c| <= finite_total_scalar_lp_norm mu 1 f*finite_total_scalar_lp_norm mu +oo g)%R.
Proof.
move=> hf hg.
pose b := finite_total_scalar_lp_norm mu +oo g.
have hb : (0 <= b)%R.
  apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm +oo g hg.1 hg.2.1).
have hbg : measure_almost_everywhere mu [set x | (`|g x| <= b)%R].
  have hh := @measure_essential_norm_almost_bound R X _ mu hm (fun y : R => `|y|%R)
    (total_scalar_function g) (measurable_function_domain hg.2.1).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hh)=> x [y [hy hle]].
  change (is_true ((`|y|%R)%:E <= total_scalar_lp_norm mu +oo g)) in hle.
  rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm +oo g hg) lee_fin in hle.
  change (is_true ((`|g x| <= b)%R)).
  by rewrite (hy : g x=y).
have [c [hci hc]] := @total_scalar_pairing_bounded_factor R X mu hm f g b hf hg.2.1 hb hbg.
exists c; split=> //; by rewrite mulrC.
Qed.
