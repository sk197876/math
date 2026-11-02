(** Federer (1969), 2.3.8, p. 78: for a finite measure on the whole source,
    almost-everywhere convergence implies convergence in measure. Source
    editions: MeasurableNormedFunctionUP.v. Federer cites 2.3.7; we reuse
    precisely its decreasing exceptional-tail estimate. Only one threshold
    at a time is needed here, so the simultaneous uniform-set selection is
    unnecessary. Essential separability supplies measurable tails without
    assuming the whole target separable. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP
  PartialNormedArithmetic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureContinuityAbove MeasurableNormedFunctionUP MeasurableNormedDeviation
  MeasurableMetricDistance MetricDeviationTails MeasureGauge MeasureConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_normed_deviation_tail_small]:
    supporting Egoroff-tail estimate for Federer 2.3.8,
    p. 78, with the finite whole-source hypothesis. *)
Lemma finite_measure_normed_deviation_tail_small (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) (e d : R) :
  (forall n, is_measurable_normed_function mu (f n)) -> is_measurable_normed_function mu g ->
  mu setT < +oo -> measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  (0 < e)%R -> (0 < d)%R ->
  exists k, mu (partial_metric_deviation_tail f g e k) < d%:E.
Proof.
move=> hf hg hfin hlim he hd.
pose F k := partial_metric_deviation_tail f g e k.
have hmF k : measure_measurable mu (F k) :=
  @measurable_normed_deviation_tail R X V N hN mu hm f g e k hf hg.
have hmono n m : (n <= m)%N -> F m `<=` F n.
  exact: partial_metric_deviation_tail_antitone.
have hfin0 : mu (F 0%N) < +oo.
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X mu hm)=> x hx; exact Logic.I.
have hz : mu (\bigcap_k F k) = 0.
  apply: (@measure_null_subset R X mu hm _ (~` partial_function_limit_locus f g) _ hlim).
  exact: partial_metric_limit_avoids_tail_intersection.
have hc := @measure_continuity_above R X mu hm F hmF hmono hfin0.
have hp : mu (\bigcap_k F k) < d%:E by rewrite hz lte_fin.
have [k hk] := hc.2.2 d%:E hp; exists k; exact: hk k (leqnn k).
Qed.

(** Source for [finite_measure_almost_convergence_in_measure]: direct
    convergence implication in Federer 2.3.8, p. 78 Arbitrary normed targets
    are allowed under the defining essential-separability condition; Banach
    completeness is unnecessary for this implication. *)
Theorem finite_measure_almost_convergence_in_measure (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) -> is_measurable_normed_function mu g ->
  mu setT < +oo -> measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  converges_in_measure mu N f g.
Proof.
move=> hf hg hfin hlim e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [k hk] := @finite_measure_normed_deviation_tail_small R X V N hN mu hm
  f g (e/2)%R (e/2)%R hf hg hfin hlim he2 he2.
exists k=> n hn.
have hsub : partial_norm_superlevel N (partial_vector_subtract (f n) g) (e/2)%:E `<=`
    partial_metric_deviation_tail f g (e/2)%R k.
  move=> x [z [hz hzbig]].
  have [a [b [ha [hb heq]]]] := proj1 (partial_vector_subtract_graph (f n) g x z) hz.
  exists n=> //; exists a,b; split=> //; split=> //.
  have hz' : (e/2 < N z)%R := hzbig; rewrite heq in hz'.
  exact: ltW hz'.
have hfeas : measure_gauge_feasible mu N (partial_vector_subtract (f n) g) (e/2)%:E.
  split; first exact: ltW he2.
  exact: le_trans (@measure_mono R X mu hm _ _ hsub) (ltW hk).
apply: le_lt_trans (@measure_gauge_bound R X V mu N _ _ hfeas) _.
rewrite lte_fin ltr_pdivrMr ?ltr0n // mulr_natr.
by rewrite ltrDl.
Qed.
