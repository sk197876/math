(** Federer (1969), 2.10.24, pp. 186–188: supporting countable assembly law
    for the limiting weighted functional, used to expand the final
    paragraph's reference to 2.10.8, p. 175. Choose increasingly fine
    near-minimal weighted covers with summable errors; the proved assembly
    theorem removes infinite aggregate weights only on a final-measure null
    set. This is an infrastructure lemma, not a claim that the fixed-cutoff
    functional is countably subadditive. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedCoverCutoffs
  FineWeightedCoverAssembly CaratheodoryLimitUP CaratheodoryLimitMeasure
  MetricDiameter
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd GeometricErrorBudget ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_cutoff_countable_limit_bound]: supporting
    countable assembly for the final paragraph of 2.10.24,
    p. 188. A fixed-cutoff infimum is bounded by the
    sum of limiting functionals of a dominating sequence.
    This does not replace the limiting functionals by
    fixed-cutoff values. No measurability of the inputs
    or finiteness of their total sum is assumed. *)
Theorem weighted_cutoff_countable_limit_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (f : X -> \bar R) (F : nat -> X -> \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> 0<delta ->
  measure_almost_everywhere psi [set x | f x<=nonnegative_sum setT (fun n=>F n x)] ->
  weighted_metric_envelope S c psi delta f<=
    nonnegative_sum setT (fun n=>weighted_metric_limit S c psi (F n)).
Proof.
move=> hpsi hc hd hdom.
have hm := caratheodory_limit_is_measure hpsi hc.
pose L := weighted_metric_limit S c psi.
have hL := weighted_metric_limit_specification S c psi.
have hL0 n : 0<=L (F n) := weighted_metric_limit_nonnegative hL (F n).
pose M := nonnegative_sum setT (fun n=>L (F n)).
change (weighted_metric_envelope S c psi delta f<=M).
case: (ltP M +oo)=> [hMfin|hMinf]; last exact: le_trans (leey _) hMinf.
have hM0 : 0<=M := nonnegative_sum_nonnegative _ _.
have hMreal : M \is a fin_num by rewrite (ge0_fin_numE hM0).
pose q := fine M.
have hM : M=q%:E by rewrite /q fineK.
rewrite hM.
have [r [hr hfine]] := positive_cofinal_metric_cutoffs hd.
apply: (@extended_upper_bound_from_scaled_errors R _ q 1%R (@ler01 R))=> e he.
pose b n := geometric_error_budget e n.
have hb n : (0<b n)%R := geometric_error_budget_positive n he.
pose lambda n := weighted_metric_envelope S c psi (r n)%:E.
have hl n := weighted_metric_envelope_specification S c psi (r n)%:E.
have hrE n : 0<(r n)%:E by rewrite lte_fin; exact: (hr n).1.
have hLnfin n : L (F n)< +oo.
  exact: le_lt_trans (nonnegative_sum_term _ (Logic.I : setT n)) hMfin.
have hnear n : lambda n (F n)<L (F n)+(b n)%:E.
  have hh := @weighted_metric_limit_upper R X J S c psi L hL (F n) (r n)%:E
    (lambda n) (hrE n) (hl n).
  have hnreal : L (F n) \is a fin_num by rewrite (ge0_fin_numE (hL0 n)).
  apply: le_lt_trans hh _.
  rewrite -{1}[L (F n)]adde0 lteD2lE // lte_fin; exact: hb.
have hex n := weighted_metric_envelope_approximation (hl n) (hnear n).
pose G n := projT1 (cid (hex n)).
pose a n := projT1 (cid (projT2 (cid (hex n)))).
have hcover n : is_weighted_metric_cover S psi (r n)%:E (F n) (G n) (a n) /\
    weighted_generator_cost c (G n) (a n)<L (F n)+(b n)%:E.
  exact: projT2 (cid (projT2 (cid (hex n)))).
pose T := nonnegative_sum setT (fun n=>weighted_generator_cost c (G n) (a n)).
have hT : T<=M+(e/2)%:E.
  have hh : T<=nonnegative_sum setT (fun n=>L (F n)+(b n)%:E).
    apply: nonnegative_sum_mono=> n _; exact: ltW (hcover n).2.
  rewrite nonnegative_sum_add in hh; last 2 first.
  - move=> n _; exact: hL0.
  - move=> n _; rewrite lee_fin; exact: ltW (hb n).
  apply: le_trans hh _; apply: leeD; first exact: lexx _.
  exact: geometric_error_sum_bound he.
have hTfin : T< +oo by apply: le_lt_trans hT _; rewrite hM -EFinD ltry.
have hdiam n j (hj : G n j) : extended_metric_diameter (S j)<=delta.
  exact: le_trans (weighted_metric_cover_diameter (hcover n).1 hj) (hr n).2.
have hfineG t (ht : (0<t)%R) : exists N, forall n j, (N<=n)%N -> G n j ->
    extended_metric_diameter (S j)<=t%:E.
  have [N hN] := hfine t ht; exists N=> n j hn hj.
  apply: le_trans (weighted_metric_cover_diameter (hcover n).1 hj) _.
  rewrite lee_fin; exact: hN n hn.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] psi hm setT
  (fun n=>[set x | F n x<=weighted_generator_sum S (G n) (a n) x]) (countableP _)
  (fun n _=>weighted_metric_cover_dominates (hcover n).1).
have hdomG : measure_almost_everywhere psi [set x | f x<=
    nonnegative_sum setT (fun n=>weighted_generator_sum S (G n) (a n) x)].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _
    (measure_almost_everywhere_and hm hdom hall))=> x [hx hxall].
  apply: le_trans hx _; apply: nonnegative_sum_mono=> n _; exact: hxall n Logic.I.
have [H [u [hu hcost]]] := @fine_weighted_cover_assembly R X J S c psi delta f G a hpsi hc
  (fun n=>weighted_metric_cover_countable (hcover n).1)
  (fun n=>weighted_metric_cover_nonnegative (hcover n).1) hdiam hfineG hTfin hdomG.
have hh := le_trans (weighted_metric_envelope_lower
  (weighted_metric_envelope_specification S c psi delta) hu) (le_trans hcost hT).
rewrite hM -EFinD in hh.
apply: le_trans hh _; rewrite mul1r lee_fin; have he2 : (e/2<=e)%R by lra.
exact: lerD (lexx q) he2.
Qed.

(** Source for [weighted_limit_countable_subadditivity]: supporting
    limiting countable subadditivity for the final paragraph
    of 2.10.24, p. 188. The almost-everywhere domination
    premise allows all inputs to be nonmeasurable and
    retains the original finite-real covering weights. *)
Theorem weighted_limit_countable_subadditivity (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (F : nat -> X -> \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) ->
  measure_almost_everywhere psi [set x | f x<=nonnegative_sum setT (fun n=>F n x)] ->
  weighted_metric_limit S c psi f<=nonnegative_sum setT (fun n=>weighted_metric_limit S c psi (F n)).
Proof.
move=> hpsi hc hdom.
apply: (weighted_metric_limit_least (weighted_metric_limit_specification S c psi))=> delta lambda hd hl.
have he := weighted_metric_envelope_unique hl (weighted_metric_envelope_specification S c psi delta).
rewrite he; exact: weighted_cutoff_countable_limit_bound hpsi hc hd hdom.
Qed.
