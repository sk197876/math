(** Federer (1969), 2.4.12, p. 87: the scalar evaluations defining sigma(f)
    on Y*. it has no integration chapter. These integrals are the scalar
    data for the subsequent vector existence proof, not an assumed vector
    integral. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAbsolute MeasureIntegralComparison
  MeasureAbsoluteSummability MeasureUpperIntegralScale MeasureIntegralScaleLaw
  MeasureLpNorm MeasureLpMembershipUP MeasureLoneNormIntegral
  ContinuousRealFunctional ContinuousRealFunctionalBound MeasureVectorIntegralUP MeasurableFunctionalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_functional_integral_exists]: supporting existence
    and bound for sigma(f)(alpha) in Federer 2.4.12, p. 87 Any positive norm
    bound on alpha suffices; no selected operator norm is required. *)
Theorem bounded_functional_integral_exists (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (a : {linear V -> R^o}) (C : R) :
  is_measure_lp_function mu 1%R f -> is_continuous_real_functional hN a ->
  (0 < C)%R -> (forall y, (`|a y| <= C*N y)%R) ->
  exists r : R, is_measure_integral mu (partial_functional_evaluation f a) r%:E /\
    `|r|%:E <= C%:E * measure_lp_norm mu N 1%R f.
Proof.
move=> hf ha hC hab.
have hn := @measure_lp_norm_nonnegative R X V N hN mu 1%R f hm hf.1 hf.2.1.1.
have hfin : measure_lp_norm mu N 1%R f \is a fin_num by rewrite (ge0_fin_numE hn); exact hf.2.2.1.
pose b := fine (measure_lp_norm mu N 1%R f).
have hb : measure_lp_norm mu N 1%R f = b%:E by rewrite fineK.
have hni := @measure_lone_norm_integral R X V N hN mu hm f hf.
have hci := @measure_integral_positive_scale R X mu hm C _ _ hC hni.
pose H := partial_extended_function_scale C (partial_norm_power N 1%R f).
have hHs : is_measure_summable mu H.
  exists (C*b)%R; by move: hci; rewrite hb -EFinM.
have heval := @measurable_functional_evaluation R X V N hN mu hm f a hf.2.1.1 ha.
have hdom : measure_almost_everywhere mu (partial_extended_le_locus
  (partial_extended_function_absolute_value (partial_functional_evaluation f a)) H).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf.2.1.1)).
  move=> x [y hy]; exists `|a y|%:E,(C*N y)%:E; split.
  - exists (a y)%:E; split; first by exists y; split.
    by rewrite abse_EFin.
  - split.
    + exists (N y)%:E; split; last by rewrite EFinM.
      exists y; split=> //; by rewrite real_power_one_exponent //; exact: real_seminorm_nonnegative hN.1 _.
    + rewrite lee_fin; exact: hab.
have [[r hr] _] := @measure_dominated_summable R X mu hm _ H heval hHs hdom.
have [s [hs hbound]] := @measure_integral_absolute_bound R X mu hm _ r%:E hr.
exists r; split=> //.
rewrite -abse_EFin; apply: le_trans hbound _.
exact (@measure_integral_monotone R X mu hm _ H _ _ hs hci hdom).
Qed.

(** Source for [continuous_functional_evaluation_summable]: direct existence
    of every scalar integral defining sigma(f) in Federer 2.4.12, p. 87 The
    finite bound is derived from continuity, not assumed. *)
Corollary continuous_functional_evaluation_summable (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (a : {linear V -> R^o}) :
  is_measure_lp_function mu 1%R f -> is_continuous_real_functional hN a ->
  is_measure_summable mu (partial_functional_evaluation f a).
Proof.
move=> hf ha; have [C [hC hb]] := continuous_real_functional_bound ha.
have [r [hr _]] := @bounded_functional_integral_exists R X V N hN mu hm f a C hf ha hC hb.
by exists r.
Qed.
