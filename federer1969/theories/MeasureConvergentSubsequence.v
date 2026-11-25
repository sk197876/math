(** Federer (1969), 2.5.5, p. 97: two applications of 2.3.10, p. 80, produce
    a subsequence with the two prescribed almost-everywhere limits. Partial
    domains remain explicit throughout. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedFunctionUP MeasureConvergenceUP
  MeasureConvergentCauchy MeasureFunctionCompleteness MeasureConvergenceLimitUniqueness MeasureConvergenceSubsequenceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergent_in_measure_almost_subsequence]: the
    prescribed-limit version of Federer 2.3.10, p. 80, used in 2.5.5, p. 97
    Completeness supplies a limit, then the proved uniqueness in measure
    identifies it almost everywhere. *)
Theorem convergent_in_measure_almost_subsequence (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu g -> converges_in_measure mu N f g ->
  exists s : nat -> nat, (forall n, (s n < s n.+1)%N) /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun n => f (s n)) g).
Proof.
move=> hf hg hfg.
have hc := @convergent_in_measure_cauchy R X V N hN mu hm f g hf hg hfg.
have [h [s [hh [hs [ha [_ hfh]]]]]] := @measurable_function_space_complete R X V N hN hY mu hm f hf hc.
have he := @convergent_in_measure_limits_almost_equal R X V N hN mu hm f h g hf hh hg hfh hfg.
exists s; split; first exact: hs.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ ha he)).
move=> x [[u [y [hu [hy hl]]]] [z [hz hgz]]].
have hzy : z=y := partial_function_single_valued hz hy.
exists u,y; split; first exact: hu.
split; [by rewrite -hzy|exact: hl].
Qed.

(** Source for [two_measures_common_almost_subsequence]: the two consecutive
    extractions in Federer 2.5.5, p. 97 Each measure may have infinite total
    mass and different null sets. The output retains its two strict index
    selections explicitly. *)
Theorem two_measures_common_almost_subsequence (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g h : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) -> is_measurable_normed_function mu g ->
  (forall n, is_measurable_normed_function nu (f n)) -> is_measurable_normed_function nu h ->
  converges_in_measure mu N f g -> converges_in_measure nu N f h ->
  exists s t : nat -> nat, (forall n, (s n < s n.+1)%N) /\ (forall n, (t n < t n.+1)%N) /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun n => f (s (t n))) g) /\
    measure_almost_everywhere nu (partial_function_limit_locus (fun n => f (s (t n))) h).
Proof.
move=> hf hg hfn hh hfg hfh.
have [s [hs hsa]] := @convergent_in_measure_almost_subsequence R X V N hN hY mu hm f g hf hg hfg.
have hfs := @converges_in_measure_subsequence R X V nu N f h s hs hfh.
have [t [ht hta]] := @convergent_in_measure_almost_subsequence R X V N hN hY nu hn
  (fun n => f (s n)) h (fun n => hfn (s n)) hh hfs.
exists s,t; split; first exact: hs.
split; first exact: ht.
split; last exact: hta.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hsa).
exact: (@partial_limit_locus_subsequence X [the topologicalType of real_norm_metric_space hN]
  (fun n => f (s n)) g t ht).
Qed.
