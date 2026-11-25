(** Federer (1969), 2.4.12, pp. 87–88: the L1 norm is the integral of the
    pointwise norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasureIntegralUP MeasureLpNorm MeasureLpMembershipUP MeasureLpPowerIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lone_norm_integral]: direct identification of
    phi_(1)(f) with integral |f| in Federer 2.4.12, pp. 86–88.
    The powered-norm graph at exponent one retains the partial domain. *)
Lemma measure_lone_norm_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu 1%R f ->
  is_measure_integral mu (partial_norm_power N 1%R f) (measure_lp_norm mu N 1%R f).
Proof.
move=> hf.
have hn := @measure_lp_norm_nonnegative R X V N hN mu 1%R f hm hf.1 hf.2.1.1.
have hfin : measure_lp_norm mu N 1%R f \is a fin_num by rewrite (ge0_fin_numE hn); exact hf.2.2.1.
have ha : measure_lp_norm mu N 1%R f = (fine (measure_lp_norm mu N 1%R f))%:E by rewrite fineK.
have hi := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm 1%R _ f hf.1 hf.2.1.1 ha.
have ha0 : (0 <= fine (measure_lp_norm mu N 1%R f))%R by move: hn; rewrite ha lee_fin.
by rewrite real_power_one_exponent // fineK in hi.
Qed.
