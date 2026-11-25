(** Federer (1969), 2.4.12, pp. 87–88: completeness of Y and continuity of
    the vector integral on the subspace with representing vectors. The
    following supporting limit lemma supplies the target vector;
    identification of its dual evaluations is separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  MeasureUP MeasureLpConvergence MeasureVectorIntegralUP MeasureVectorIntegralDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_cauchy]: supporting Cauchy transfer
    for the closed-subspace argument in Federer 2.4.12, pp. 87–88 *)
Lemma measure_vector_integral_cauchy (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (y : nat -> real_norm_metric_space hN) :
  (forall n, is_measure_vector_integral mu (f n) (y n)) ->
  cauchy_in_lp_norm mu N 1%R f -> cauchy (y @ \oo).
Proof.
move=> hi hc.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter (y @ \oo) := @fmap_proper_filter nat (real_norm_metric_space hN) y \oo PF0.
apply: (proj2 (@cauchyP R [the metricType R of real_norm_metric_space hN] (y @ \oo) PF))=> epsilon he.
have [K hK] := hc epsilon he; exists (y K).
exists K; first exact I.
move=> m hmK.
rewrite ballEmdist.
change (is_true (N (y K-y m) < epsilon)%R).
have hb := @measure_vector_integral_distance_bound R X V N hN mu hm (f K) (f m) (y K) (y m) (hi K) (hi m).
have ht := le_lt_trans hb (hK K m (leqnn K) hmK).
by move: ht; rewrite lte_fin.
Qed.

(** Source for [measure_vector_integral_cauchy_limit]: supporting
    use of Banach completeness in Federer 2.4.12, pp. 87–88.
    Integral witnesses of an L1 Cauchy sequence converge in Y.
    This does not yet assert that the limit represents any given function. *)
Lemma measure_vector_integral_cauchy_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (y : nat -> real_norm_metric_space hN) :
  (forall n, is_measure_vector_integral mu (f n) (y n)) ->
  cauchy_in_lp_norm mu N 1%R f -> exists z : real_norm_metric_space hN, y @ \oo --> z.
Proof.
move=> hi hc.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter (y @ \oo) := @fmap_proper_filter nat (real_norm_metric_space hN) y \oo PF0.
exact (@hY (y @ \oo) PF (@measure_vector_integral_cauchy R X V N hN mu hm f y hi hc)).
Qed.
