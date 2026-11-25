(** Federer (1969), 2.4.12, pp. 87–88: zero in the subspace carrying the
    vector integral. The zero function is integrable even when the ambient
    measure is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedBasic
  MeasureLpNorm MeasureLpZero MeasureLpMembershipUP CountablyMeasurableFunctions
  MeasureConullZeroIntegral MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_total_zero_membership]: supporting zero
    member of Lp in Federer 2.4.12, pp. 86–87, for every
    finite p>=1 and arbitrary ambient measure. *)
Lemma measure_lp_total_zero_membership (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) :
  (1 <= p)%R -> is_measure_lp_function mu p
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN))).
Proof.
move=> hp; pose f := partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)).
have hA := @measurable_normed_total_constant R X V N hN mu hm 0%R.
have hn : measure_lp_norm mu N p f = 0.
  apply: (@lp_norm_zero_iff R X V N hN mu hm p f hp hA.1).2.
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  by move=> x _; exists 0%R; split.
split=> //; split=> //; split; first by rewrite hn ltry.
exact: countably_measurable_zero_function hm _.
Qed.

(** Source for [measure_vector_integral_zero]: direct zero case of the
    linear vector integral in Federer 2.4.12, pp. 87–88 No finite source
    measure is needed. *)
Theorem measure_vector_integral_zero (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_vector_integral mu
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN))) 0%R.
Proof.
split; first exact (@measure_lp_total_zero_membership R X V N hN mu hm 1%R (lexx _)).
move=> a ha; rewrite linear0; apply: (@measure_almost_zero_integral R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists (0%R : V); split=> //; by rewrite linear0.
Qed.
