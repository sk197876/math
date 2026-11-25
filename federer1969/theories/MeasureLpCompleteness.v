(** Federer (1969), 2.4.12, p. 87: the finite-p completeness argument
    through convergence in measure and an almost-everywhere convergent
    subsequence. These statements retain partial domains and allow infinite
    individual norms; membership in the finite-norm Lebesgue space is a
    separate condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionLimitUP
  PartialNormedArithmetic PartialDifferenceLimit MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFunctionCompleteness
  MeasureLpNorm MeasureLpNormLowerLimit MeasureLpConvergence MeasurableNormedDifference
  ExtendedLowerLimit ExtendedLowerLimitUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_norm_cauchy_complete]: the complete finite-p
    Cauchy-to-limit argument in Federer 2.4.12, p. 87 This theorem first
    gives completeness in A with its possibly infinite pseudodistance;
    finite-norm and countable-measurability membership are handled
    separately for the Lebesgue-space claim. *)
Theorem lp_norm_cauchy_complete (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (forall n, is_measurable_normed_function mu (f n)) ->
  cauchy_in_lp_norm mu N p f ->
  exists (h : partial_function X (real_norm_metric_space hN)) (s : nat -> nat),
    is_measurable_normed_function mu h /\ (forall n, (s n < s n.+1)%N) /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun n => f (s n)) h) /\
    converges_in_lp_norm mu N p f h.
Proof.
move=> hp hf hc.
have [h [s [hh [hs [hl _]]]]] := @measurable_function_space_complete R X V N hN hY mu hm f
  hf (@lp_norm_cauchy_in_measure R X V N hN mu hm p f hp hf hc).
exists h,s; split=> //; split=> //; split=> //.
have hsn n : (n <= s n)%N.
  elim: n=> [|n ih]; first exact: leq0n.
  have hstep : (n.+1 <= (s n).+1)%N := ih.
  exact: leq_trans hstep (hs n).
move=> e he; have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK] := hc (e/2)%R he2; exists K=> n hn.
have hdn := measurable_function_domain (hf n).1.
have hlim := @partial_difference_almost_limit R X V N hN mu hm (f n) (fun j => f (s j)) h hdn hl.
have hb := @measure_lp_norm_lower_semicontinuous R X V N hN mu hm p
  (fun j => partial_vector_subtract (f n) (f (s j))) (partial_vector_subtract (f n) h) hp
  (fun j => (@measurable_normed_function_subtract R X V N hN mu hm _ _ (hf n) (hf (s j))).1)
  (@measurable_normed_function_subtract R X V N hN mu hm _ _ (hf n) hh).1 hlim.
apply: le_lt_trans hb _.
apply: (le_lt_trans (y:= (e/2)%:E)).
- apply: extended_lower_limit_eventual_upper_bound (extended_lower_limit_laws _) _.
  exists K=> j hj; exact: ltW (hK n (s j) hn (leq_trans hj (hsn j))).
- have htwo : (0 < 2 :> R)%R by rewrite ltr0n.
  rewrite lte_fin (@ltr_pdivrMr R 2%R e e htwo).
  by rewrite -{1}[e]mulr1 ltr_pM2l // ltr1n.
Qed.
