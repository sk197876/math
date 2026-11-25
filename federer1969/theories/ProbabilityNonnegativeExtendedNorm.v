(** Supporting full exponent comparison for Federer (1969), 2.10.5, p. 173,
    normalized integral-geometric measures. Apply the probability norm
    comparison of 2.4.17, p. 90, to nonnegative extended inputs without
    assuming boundedness. If the larger norm is infinite the comparison is
    immediate. Otherwise prove finite input values almost everywhere first;
    exact null-modification invariance then permits the existing scalar
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology ScalarNormExtendedEmbedding
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic NonnegativeExtendedExponentNorm
  NonnegativeExtendedScalarNorm NonnegativeExtendedNormAlmostEquality
  NonnegativeExtendedNormFiniteValues MeasureExponentDomain ProbabilityExponentMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_norm_almost_finite_scalar]:
    supporting exact scalar reduction for the
    exponent comparison in Federer 2.10.5,
    p. 173. Infinite inputs are replaced only
    after their exceptional locus is proved null. *)
Theorem nonnegative_extended_norm_almost_finite_scalar (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> measure_almost_everywhere mu [set x | f x \is a fin_num] ->
  1<=t -> is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu f t =
    measure_exponent_norm mu (partial_function_total
      (fun x => (fine (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))) t.
Proof.
move=> hf0 hfinite ht hf.
pose g (x : X) : real_norm_metric_space (scalar_absolute_value_norm R) := fine (f x).
have hg0 x : (0<=g x)%R.
  rewrite /g; have h := hf0 x; by case: (f x) h=> [r| |] //=; rewrite lee_fin.
have hg := @measurable_extended_finite_scalar R X mu hm f hf.
have hge : @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x => (g x)%:E)).
  apply: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hm g (fun y => y%:E) hg).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hae : measure_almost_everywhere mu [set x | f x=(g x)%:E].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfinite)=> x hx.
  exact: esym (fineK hx).
rewrite (@nonnegative_extended_norm_almost_equal R X mu hm f (fun x => (g x)%:E) t
  hf0 (fun x => hg0 x) ht hf hge hae).
exact: (@nonnegative_extended_norm_scalar_embedding R X mu hm g t hg0 ht hg).
Qed.

(** Source for [probability_nonnegative_extended_norm_monotone]:
    supporting comparison of all normalized gauge
    costs in Federer 2.10.5, p. 173, from
    the probability assertion of 2.4.17, p. 90.
    Unbounded inputs, infinite values and the
    infinity exponent are included. *)
Theorem probability_nonnegative_extended_norm_monotone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (s t : \bar R) :
  mu setT = 1 -> (forall x, 0<=f x) -> 1<=s -> s<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu f s<=nonnegative_extended_exponent_norm mu f t.
Proof.
move=> hprob hf0 hs hst hf; have ht := le_trans hs hst.
case: (ltP (nonnegative_extended_exponent_norm mu f t) +oo)=> [hfin|hfin]; last first.
  exact: le_trans (leey _) hfin.
have hn := @nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf.
have hae := @finite_nonnegative_extended_norm_almost_finite R X mu hm f t _ hf0 hn hfin.
rewrite (@nonnegative_extended_norm_almost_finite_scalar R X mu hm f s hf0 hae hs hf)
  (@nonnegative_extended_norm_almost_finite_scalar R X mu hm f t hf0 hae ht hf).
exact: (@probability_measure_exponent_norm_monotone R X mu hm _ s t hprob hs hst
  (@measurable_extended_finite_scalar R X mu hm f hf)).
Qed.
