(** Federer (1969), 2.10.24(2), pp. 187–188: the positive-level bound makes
    the positive support a countable union of finite-measure sets, so part
    (1) applies. Continuity below is supplied separately by 2.10.22 in the
    direct compact-cost theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds IncreasingProjectionLoss
  MetricDiameter MetricScaleEnvelopeUP CaratheodoryLimitUP CaratheodoryWeakEnlargementUP
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedUpperIntegralBound WeightedSigmaFiniteEquality
  WeightedLimitLevelBound ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_limit_continuous_scale_equality]:
    supporting equality argument in 2.10.24(2),
    pp. 187–188, with continuity below isolated as
    its precise proof input. The weak enlargement
    formulation also permits zero generator costs;
    the direct strict statement is a corollary. *)
Theorem weighted_metric_limit_continuous_scale_equality (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R) (E : set X -> set X) (k : R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) :
  is_weak_caratheodory_enlargement F c E k ->
  (forall S, F S -> S<>set0) ->
  (forall S, F S -> extended_metric_diameter S< +oo -> c S< +oo) ->
  (forall S, F S -> closed S) ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  is_weighted_metric_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi L ->
  (forall (d : R) nu, (0<d)%R ->
    is_metric_scale_envelope (fun j : set_type F=>val j) (fun j=>c (val j)) d%:E nu ->
    has_increasing_set_continuity nu) ->
  (forall x, 0<=f x) -> L f=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hE hne hcf hclosed hp hL hcont hf.
have hc (j : set_type F) := weak_enlargement_cost_nonnegative hE (set_valP j).
have hupper := @weighted_metric_limit_upper_integral_bound R X [the choiceType of set_type F]
  (fun j=>val j) (fun j=>c (val j)) psi L f hp hc hL hf.
apply/eqP; rewrite eq_le hupper /=.
have hnon := weighted_metric_limit_nonnegative hL f.
case hval : (L f)=> [M| |] in hnon *; [|exact: leey|by []].
pose t n := ((n.+1%:R : R)^-1)%R.
pose A n := [set x | (t n)%:E<f x].
have ht n : (0<t n)%R by rewrite /t invr_gt0 ltr0n.
have hLM : L f<=M%:E by rewrite hval.
have hfinite n : psi (A n)< +oo.
  have hh := @weighted_limit_positive_level_bound R X F c psi E k L f M (t n)
    hE hne hcf hp hL hcont hLM (ht n).
  exact: le_lt_trans hh (ltry _).
have hsupport : [set x | 0<f x] `<=` \bigcup_n A n.
  move=> x hx; have [N hN] := (@reciprocal_natural_order_limit R).2 (f x) hx.
  exists N=> //; exact: hN N (leqnn N).
have heq := @weighted_metric_limit_sigma_finite_equality R X F c psi E k L f A hE hp hL hclosed hf hfinite hsupport.
by rewrite -heq hval.
Qed.
