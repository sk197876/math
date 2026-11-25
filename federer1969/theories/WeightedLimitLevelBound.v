(** Federer (1969), 2.10.24(2), pp. 187–188: positive-level measure estimate
    from finite weighted limit. Continuity below of the positive-cutoff
    approximating measures is the precise input used from 2.10.22. The
    theorem retains arbitrary nonmeasurable f. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import ExtendedRealOrderTopology MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope
  MetricScaleCutoffCost CaratheodoryLimitUP CaratheodoryWeakEnlargementUP MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP
  IncreasingProjectionLoss CountableWeightedEnlargementBound WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedCoverCutoffs ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_limit_positive_level_bound]: supporting
    psi({f>t})<=k lim(lambda_delta(f))/t in
    2.10.24(2), pp. 187–188, in finite-upper-bound
    form. An arbitrary uniform enlargement control k
    replaces the separate printed constants five and eta.
    This bound suffices to cover the positive support
    by sets of finite measure. *)
Theorem weighted_limit_positive_level_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R) (E : set X -> set X) (k : R)
    (L : (X -> \bar R) -> \bar R) (f : X -> \bar R) (M t : R) :
  is_weak_caratheodory_enlargement F c E k ->
  (forall S, F S -> S<>set0) ->
  (forall S, F S -> extended_metric_diameter S< +oo -> c S< +oo) ->
  is_caratheodory_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi ->
  is_weighted_metric_limit (fun j : set_type F=>val j) (fun j=>c (val j)) psi L ->
  (forall (d : R) nu, (0<d)%R ->
    is_metric_scale_envelope (fun j : set_type F=>val j) (fun j=>c (val j)) d%:E nu ->
    has_increasing_set_continuity nu) ->
  L f<=M%:E -> (0<t)%R -> psi [set x | t%:E<f x]<=(k*M/t)%R%:E.
Proof.
move=> hE hne hfinite hp hL hcont hLM ht.
pose J := [the choiceType of set_type F].
have hk := weak_enlargement_constant_positive hE.
have hc (j : J) := @weak_enlargement_cost_nonnegative R X F c E k hE (val j) (set_valP j).
have hkdiv : (0<=k/t)%R := divr_ge0 (ltW hk) (ltW ht).
apply: (@extended_upper_bound_from_scaled_errors R _ (k*M/t)%R (k/t)%R hkdiv)=> e he.
have hrewrite : (k*(M+e)/t=k*M/t+(k/t)*e)%R by field; rewrite gt_eqF.
rewrite -hrewrite.
apply: (caratheodory_limit_least hp)=> eta nu heta hn.
have [r [hr hcofinal]] := @positive_cofinal_metric_cutoffs R eta heta.
pose d := (r 0%N/k)%R.
have hd : (0<d)%R by rewrite /d divr_gt0 //; exact: (hr 0%N).1.
have hkd : (k*d=r 0%N)%R by rewrite /d mulrC divfK ?gt_eqF.
have hkdpos : (0<k*d)%R by rewrite hkd; exact: (hr 0%N).1.
have hcut : (k*d)%R%:E<=eta by rewrite hkd; exact: (hr 0%N).2.
pose xi := metric_scale_envelope (fun j : J=>val j) (fun j=>c (val j)) (k*d)%R%:E.
have hxi := @metric_scale_envelope_specification R X J (fun j=>val j) (fun j=>c (val j)) (k*d)%R%:E.
have hl := @weighted_metric_envelope_specification R X J (fun j=>val j) (fun j=>c (val j)) psi d%:E.
have hdE : 0<d%:E by rewrite lte_fin.
have hle := @weighted_metric_limit_upper R X J (fun j=>val j) (fun j=>c (val j)) psi L hL f d%:E _ hdE hl.
have hstrict : M%:E<(M+e)%R%:E by rewrite lte_fin; lra.
have [G [u [hGu hcost]]] := weighted_metric_envelope_approximation hl (le_lt_trans (le_trans hle hLM) hstrict).
pose V := [set x | t%:E<weighted_generator_sum (fun j : J=>val j) G u x].
have hV := @countable_weighted_enlargement_bound R X F c E k d xi G u t (M+e)%R hE hne
  (fun j hj=>hfinite (val j) (set_valP j)
    (le_lt_trans (@weighted_metric_cover_diameter R X J (fun j=>val j) psi d%:E f G u hGu j hj) (ltry d))) hxi
  (hcont (k*d)%R xi hkdpos hxi) (weighted_metric_cover_countable hGu)
  (weighted_metric_cover_diameter hGu) (weighted_metric_cover_nonnegative hGu) ht (ltW hcost).
have hnuV : nu V<=(k*(M+e)/t)%R%:E.
  apply: le_trans _ hV.
  exact (@metric_scale_envelope_antitone_cutoff R X J (fun j=>val j) (fun j=>c (val j))
    (k*d)%R%:E eta xi nu hxi hn hcut V).
pose N := ~` [set x | f x<=weighted_generator_sum (fun j : J=>val j) G u x].
have hN : psi N=0 := weighted_metric_cover_dominates hGu.
have hnu := metric_scale_envelope_is_measure hn hc.
have hnuN : nu N=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hnu) andbT.
  have hh := @caratheodory_limit_upper R X J (fun j=>val j) (fun j=>c (val j)) psi hp N eta nu heta hn.
  by rewrite hN in hh.
have hcover : [set x | t%:E<f x] `<=` V `|` N.
  move=> x hx; case: (pselect (f x<=weighted_generator_sum (fun j : J=>val j) G u x))=> hdom.
  - left; exact: lt_le_trans hx hdom.
  - by right.
have hh := @measure_binary_cover R X nu hnu [set x | t%:E<f x] V N hcover.
rewrite hnuN adde0 in hh; exact: le_trans hh hnuV.
Qed.
