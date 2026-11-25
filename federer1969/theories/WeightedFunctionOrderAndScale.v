(** Federer (1969), 2.10.24, pp. 186–188: supporting almost-everywhere order
    and positive homogeneity of the weighted infima and their limiting
    functional. Inverse scaling preserves the finite-real coefficient
    domain; no equality with an integral is assumed. These laws support the
    final-paragraph use of 2.10.8, p. 175. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimit WeightedCoverScale MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_envelope_almost_order]: supporting
    order consequence of the admissibility condition in
    2.10.24, p. 186. Inputs need not be measurable;
    their comparison holds for the actual final measure
    almost everywhere, as in the printed convention. *)
Theorem weighted_metric_envelope_almost_order (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (lambda : (X -> \bar R) -> \bar R) (f g : X -> \bar R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  measure_almost_everywhere psi [set x | f x<=g x] -> lambda f<=lambda g.
Proof.
move=> hm hl hfg; apply: (weighted_metric_envelope_greatest hl)=> G u hcover.
apply: (weighted_metric_envelope_lower hl); constructor.
- exact: weighted_metric_cover_countable hcover.
- exact: weighted_metric_cover_nonnegative hcover.
- exact: weighted_metric_cover_diameter hcover.
- apply: (@measure_almost_everywhere_mono R X psi hm _ _ _
    (measure_almost_everywhere_and hm hfg (weighted_metric_cover_dominates hcover)))=> x [h1 h2].
  exact: le_trans h1 h2.
Qed.

(** Source for [weighted_metric_limit_almost_order]: supporting
    almost-everywhere order of the actual limiting functional
    in 2.10.24, p. 187. Both inputs and limiting
    values may be infinite and need not be measurable. *)
Theorem weighted_metric_limit_almost_order (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f g : X -> \bar R) :
  is_measure psi -> is_weighted_metric_limit S c psi L ->
  measure_almost_everywhere psi [set x | f x<=g x] -> L f<=L g.
Proof.
move=> hm hL hfg; apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
apply: le_trans (@weighted_metric_envelope_almost_order R X J S c psi delta lambda f g hm hl hfg) _.
exact: (@weighted_metric_limit_upper R X J S c psi L hL g delta lambda hd hl).
Qed.

(** Source for [weighted_metric_envelope_scale_lower]: supporting
    inverse rescaling of an admissible weighted cover in
    2.10.24, p. 186. The positive scalar and all
    resulting coefficients remain finite real numbers. *)
Lemma weighted_metric_envelope_scale_lower (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (lambda : (X -> \bar R) -> \bar R) (f : X -> \bar R) (a : R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  (forall j, 0<=c j) -> (0<a)%R ->
  a%:E*lambda f<=lambda (fun x=>a%:E*f x).
Proof.
move=> hm hl hc ha; have hane : (a!=0)%R by rewrite gt_eqF.
have hai : (0<=a^-1)%R by rewrite invr_ge0; exact: ltW ha.
have haiE : 0<=(a^-1)%R%:E by rewrite lee_fin.
have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha.
apply: (weighted_metric_envelope_greatest hl)=> G u hcover.
pose v j := (a^-1*u j)%R.
have hv : is_weighted_metric_cover S psi delta f G v.
  constructor.
  - exact: weighted_metric_cover_countable hcover.
  - move=> j hj; exact: mulr_ge0 hai (weighted_metric_cover_nonnegative hcover hj).
  - exact: weighted_metric_cover_diameter hcover.
  - apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (weighted_metric_cover_dominates hcover))=> x hx.
    have hh := lee_wpmul2l haiE hx.
    change (is_true (f x<=weighted_generator_sum S G v x)).
    rewrite /v weighted_generator_sum_scale //; last exact: weighted_metric_cover_nonnegative hcover.
    by rewrite muleA -EFinM mulVf // mul1e in hh.
have hh := weighted_metric_envelope_lower hl hv.
rewrite /v weighted_generator_cost_scale in hh=> //; last exact: weighted_metric_cover_nonnegative hcover.
have hmul := lee_wpmul2l haE hh.
by rewrite muleA -EFinM mulfV // mul1e in hmul.
Qed.

(** Source for [weighted_metric_envelope_positive_scale]: supporting
    exact positive homogeneity of lambda_delta in 2.10.24,
    p. 186. Reciprocal rescaling proves both inequalities
    without assuming a minimum or finite infimum value. *)
Theorem weighted_metric_envelope_positive_scale (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (lambda : (X -> \bar R) -> \bar R) (f : X -> \bar R) (a : R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  (forall j, 0<=c j) -> (0<a)%R ->
  lambda (fun x=>a%:E*f x)=a%:E*lambda f.
Proof.
move=> hm hl hc ha.
have hane : (a!=0)%R by rewrite gt_eqF.
have hai : (0<a^-1)%R by rewrite invr_gt0.
have hh := @weighted_metric_envelope_scale_lower R X J S c psi delta lambda
  (fun x=>a%:E*f x) (a^-1)%R hm hl hc hai.
have he : (fun x=>(a^-1)%R%:E*(a%:E*f x))=f.
  by apply: funext=> x; rewrite muleA -EFinM mulVf // mul1e.
have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha.
have hmul := lee_wpmul2l haE hh.
rewrite he muleA -EFinM mulfV // mul1e in hmul.
apply/eqP; rewrite eq_le hmul /=.
exact: weighted_metric_envelope_scale_lower hm hl hc ha.
Qed.

(** Source for [weighted_metric_limit_positive_scale]: supporting
    exact positive homogeneity of the cutoff limit in
    2.10.24, p. 187, used in the final-paragraph
    Borel-partition argument on p. 188. Infinite limiting
    values are included; the scalar remains finite. *)
Theorem weighted_metric_limit_positive_scale (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> \bar R) (a : R) :
  is_measure psi -> is_weighted_metric_limit S c psi L ->
  (forall j, 0<=c j) -> (0<a)%R ->
  L (fun x=>a%:E*f x)=a%:E*L f.
Proof.
move=> hm hL hc ha; have haE : 0<=a%:E by rewrite lee_fin; exact: ltW ha.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  rewrite (@weighted_metric_envelope_positive_scale R X J S c psi delta lambda f a hm hl hc ha).
  exact: (lee_wpmul2l haE (@weighted_metric_limit_upper R X J S c psi L hL f delta lambda hd hl)).
- rewrite -lee_pdivlMl //; apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  rewrite lee_pdivlMl // -(@weighted_metric_envelope_positive_scale R X J S c psi delta lambda f a hm hl hc ha).
  exact: (@weighted_metric_limit_upper R X J S c psi L hL _ delta lambda hd hl).
Qed.
