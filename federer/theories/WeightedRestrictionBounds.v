(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting null and
    threshold laws for the abstract restricted weighted measure. Null
    restrictions admit the empty weighted cover. Positive homogeneity and
    almost-order compare positive lower levels with the weighted indicator
    value, without using an integral equality. Source context:
    WeightedRestrictionMeasureUP.v and WeightedFunctionOrderAndScale.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedRestrictionMeasureUP WeightedRestrictionMeasure
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedFunctionOrderAndScale
  WeightedRestrictionSeparation CaratheodoryLimitUP CaratheodoryLimitMeasure
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_restriction_whole]: supporting whole-space
    evaluation for the auxiliary object in 2.10.24,
    p. 188, derived from its abstract evaluation law. *)
Lemma weighted_restriction_whole (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  weighted_restriction_measure S c psi f setT=weighted_metric_limit S c psi f.
Proof.
rewrite weighted_restriction_measureE.
have he : weighted_function_restriction f setT=f.
  by apply: funext=> x; rewrite /weighted_function_restriction in_setT.
by rewrite he.
Qed.

(** Source for [weighted_restriction_null]: supporting exceptional-set
    removal for the final paragraph of 2.10.24, p. 188.
    A restriction to an original-measure null set has
    zero weighted limit, even for infinite input values. *)
Theorem weighted_restriction_null (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) A :
  is_measure psi -> psi A=0 -> weighted_restriction_measure S c psi f A=0.
Proof.
move=> hm hA; rewrite weighted_restriction_measureE.
have hL := weighted_metric_limit_specification S c psi.
have hoff : measure_almost_everywhere psi (~` A) by rewrite /measure_almost_everywhere setCK.
have hdom : measure_almost_everywhere psi [set x | weighted_function_restriction f A x<=0].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hoff)=> x hx.
  have hnx : x \notin A by apply/negP=> /set_mem hxA; exact: hx hxA.
  change (is_true (weighted_function_restriction f A x<=0)).
  by rewrite /weighted_function_restriction (negbTE hnx).
have hh := @weighted_metric_limit_almost_order R X J S c psi _
  (weighted_function_restriction f A) (fun _=>0) hm hL hdom.
rewrite (weighted_metric_limit_zero hm hL) in hh.
apply/eqP; by rewrite eq_le hh (weighted_metric_limit_nonnegative hL).
Qed.

(** Source for [weighted_restriction_threshold_bound]: supporting
    positive-threshold comparison for the final paragraph
    of 2.10.24, p. 188. The indicator identification
    is an explicitly proved input law; homogeneity and
    pointwise order give the comparison for any target,
    without assuming that target measurable. *)
Theorem weighted_restriction_threshold_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (A : set X) (t : R) :
  is_measure psi -> (forall j, 0<=c j) ->
  (forall B, weighted_restriction_measure S c psi (fun _=>1) B=psi B) ->
  (0<t)%R -> (forall x, A x -> t%:E<=f x) ->
  t%:E*psi A<=weighted_restriction_measure S c psi f A.
Proof.
move=> hm hc hind ht hlevel.
have hL := weighted_metric_limit_specification S c psi.
pose a := @weighted_function_restriction R X (fun _=>1) A.
pose b := weighted_function_restriction f A.
have hdom : measure_almost_everywhere psi [set x | t%:E*a x<=b x].
  apply: (@measure_almost_everywhere_mono R X psi hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  change (is_true (t%:E*a x<=b x)); rewrite /a /b /weighted_function_restriction.
  case hx: (x \in A); [rewrite mule1; exact: hlevel x (set_mem hx)|by rewrite mule0].
have hh := @weighted_metric_limit_almost_order R X J S c psi _ (fun x=>t%:E*a x) b hm hL hdom.
rewrite (@weighted_metric_limit_positive_scale R X J S c psi _ a t hm hL hc ht) in hh.
have he : weighted_metric_limit S c psi a=psi A.
  have h := hind A; rewrite weighted_restriction_measureE in h; exact h.
rewrite he in hh; by rewrite weighted_restriction_measureE.
Qed.

(** Source for [finite_weighted_limit_threshold_measure]: supporting
    finite-mass consequence used for lower-step fibres in
    the final paragraph of 2.10.24, p. 188. A positive
    threshold on a set and a finite limiting weighted
    value force its original measure to be finite. *)
Theorem finite_weighted_limit_threshold_measure (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (A : set X) (t : R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> (forall x, 0<=f x) ->
  (forall B, weighted_restriction_measure S c psi (fun _=>1) B=psi B) ->
  (0<t)%R -> (forall x, A x -> t%:E<=f x) -> weighted_metric_limit S c psi f< +oo -> psi A< +oo.
Proof.
move=> hpsi hc hf0 hind ht hlevel hfin.
have hm := caratheodory_limit_is_measure hpsi hc.
have hn := weighted_restriction_is_measure hpsi hc hf0.
have hmono := @measure_mono R X _ hn A setT (fun x _=>Logic.I).
rewrite weighted_restriction_whole in hmono.
have hbound := @weighted_restriction_threshold_bound R X J S c psi f A t hm hc hind ht hlevel.
have hh := le_lt_trans hbound (le_lt_trans hmono hfin).
case: (ltP (psi A) +oo)=> [hA|hA]; first by [].
have hinf : psi A=+oo by apply/eqP; rewrite eq_le leey hA.
by rewrite hinf /mule /= eqe lte_fin (gt_eqF ht) ht ltxx in hh.
Qed.
