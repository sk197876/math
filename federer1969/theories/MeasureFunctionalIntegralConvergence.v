(** Federer (1969), 2.4.12, p. 87: continuity of scalar evaluations of
    sigma(f) in the L1 seminorm. This supporting convergence theorem is
    proved from the scalar difference estimate and the finite bound supplied
    by continuity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureIntegralUP MeasureLpNorm MeasureLpMembershipUP MeasureLpConvergence MeasureLpDifferenceMembership
  ContinuousRealFunctional ContinuousRealFunctionalBound MeasureVectorIntegralUP MeasureFunctionalIntegralDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [functional_integral_converges]: supporting continuity of
    sigma in Federer 2.4.12, p. 87 Convergence is for the actual scalar
    integral values, without presupposing vector integral existence. *)
Theorem functional_integral_converges (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) (a : {linear V -> R^o})
    (r : nat -> real_line_metric R) (s : real_line_metric R) :
  (forall n, is_measure_lp_function mu 1%R (f n)) -> is_measure_lp_function mu 1%R g ->
  is_continuous_real_functional hN a ->
  (forall n, is_measure_integral mu (partial_functional_evaluation (f n) a) (r n)%:E) ->
  is_measure_integral mu (partial_functional_evaluation g a) s%:E ->
  converges_in_lp_norm mu N 1%R f g -> r @ \oo --> s.
Proof.
move=> hf hg ha hi hj hl.
have [C [hC hb]] := continuous_real_functional_bound ha.
move=> U hU.
have [epsilon he hball] := proj1 (metricType_numDomainType.nbhs_mdistP s U) hU.
have hdelta : (0 < epsilon/C)%R by rewrite divr_gt0.
have [K hK] := hl _ hdelta; exists K; first exact I.
move=> n hn; apply: hball.
have hd := @measure_lp_function_subtract R X V N hN mu hm 1%R (f n) g (hf n) hg.
have hnn := @measure_lp_norm_nonnegative R X V N hN mu 1%R _ hm hd.1 hd.2.1.1.
have hfinite : measure_lp_distance mu N 1%R (f n) g \is a fin_num.
  rewrite (ge0_fin_numE hnn); exact hd.2.2.1.
pose d := fine (measure_lp_distance mu N 1%R (f n) g).
have hed : measure_lp_distance mu N 1%R (f n) g = d%:E by rewrite fineK.
have hsmall : (d < epsilon/C)%R by have hh := hK n hn; rewrite hed lte_fin in hh.
have hbound := @functional_integral_difference_bound R X V N hN mu hm (f n) g a C (r n) s
  (hf n) hg ha hC hb (hi n) hj.
rewrite hed -EFinM lee_fin in hbound.
change (is_true (`|s-r n| < epsilon)%R); rewrite -opprB normrN.
apply: le_lt_trans hbound _.
rewrite mulrC -ltr_pdivlMr //; exact hsmall.
Qed.
