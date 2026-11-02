(** Federer (1969), 2.4.12, p. 87: continuity of sigma(f), whose values are
    scalar integrals of continuous linear evaluations. The difference
    estimate below follows from scalar linearity and the proved evaluation
    bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  PartialExtendedArithmetic DominatedErrorGraphs MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralDifference MeasureIntegralAlmostEquality
  MeasureLpMembershipUP MeasureLpConvergence MeasureLpDifferenceMembership
  ContinuousRealFunctional MeasureVectorIntegralUP MeasureFunctionalIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [functional_integral_difference_bound]: supporting continuity
    estimate for sigma in Federer 2.4.12, p. 87 This is proved for the
    scalar integrals before vector-integral existence is used. *)
Lemma functional_integral_difference_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN))
    (a : {linear V -> R^o}) (C r s : R) :
  is_measure_lp_function mu 1%R f -> is_measure_lp_function mu 1%R g ->
  is_continuous_real_functional hN a -> (0 < C)%R -> (forall y, (`|a y| <= C*N y)%R) ->
  is_measure_integral mu (partial_functional_evaluation f a) r%:E ->
  is_measure_integral mu (partial_functional_evaluation g a) s%:E ->
  `|r-s|%:E <= C%:E * measure_lp_distance mu N 1%R f g.
Proof.
move=> hf hg ha hC hb hfi hgi.
have hd := @measure_lp_function_subtract R X V N hN mu hm 1%R f g hf hg.
have [b [hbi hbound]] := @bounded_functional_integral_exists R X V N hN mu hm _ a C hd ha hC hb.
have hsub := @measure_integral_finite_difference R X mu hm _ _ r s hfi hgi.
have hdiff : is_measure_integral mu (partial_functional_evaluation (partial_vector_subtract f g) a) (r-s)%:E.
  apply: (@measure_integral_almost_equal R X mu hm _ _ _ hsub).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _
      (measurable_function_domain hf.2.1.1) (measurable_function_domain hg.2.1.1))).
  move=> x [[u hu] [v hv]]; exists (a (u-v)%R)%:E; split.
  - rewrite linearB; apply: partial_finite_difference_graph; [exists u|exists v]; by split.
  - exists (u-v)%R; split=> //; apply/partial_vector_subtract_graph; exists u,v; by split=> //; split.
have he := measure_integral_unique hbi hdiff.
have heb : b=(r-s)%R by injection he.
by rewrite heb in hbound.
Qed.
