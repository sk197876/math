(** Federer (1969), 2.9.22, pp. 167–168: extend the variation-derivative
    equality in 2.9.19(1), pp. 163–165. Norm derivative existence is proved
    separately; the fine metric partition argument identifies s'=N(g')
    almost everywhere. It has no corresponding reflexive-Banach extension,
    nor does. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP CurveArcLength CurveLipschitzFactor
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP
  NormedCurveDerivativeUP NormedDerivativeBounds NormedDerivativeDualEvaluation RealCurveDerivativeUP RealDerivativeOrder
  MetricCurveVariationDerivative MetricVariationDefect MetricVariationDefectNullity
  NormedVariationDefectCover ReflexiveBVDifferentiation MonotoneStieltjesDifferentiation
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealMetricBackground CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_bv_derivative_variation_bound]: supporting
    inequality N(g')<=s' for Federer 2.9.22, pp. 167–168,
    extending the lower comparison in 2.9.19, pp. 164–165.
    Pass the distance/variation bound to the actual finite norm and
    scalar derivative limits. The nonnegative parameter derivative
    is explicit in this local lemma and is proved almost everywhere
    by monotonicity in the theorem below. *)
Lemma normed_bv_derivative_variation_bound (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g : R -> real_norm_metric_space hN) (x w : R) (v : E) :
  curve_locally_finite_variation g -> has_normed_curve_derivative N g x v ->
  has_real_curve_derivative (arc_length g) x w -> 0<=w -> N v<=w.
Proof.
move=> hg hG hS hw.
have hNorm := punctured_norm_limit_norm hN hG.
have hAbs := punctured_real_limit_absolute hS.
rewrite (ger0_norm hw) in hAbs.
apply: (@punctured_real_limit_order R (fun h => N (h^-1 *: (g (x+h)-g x)))
  (fun h => `|(arc_length g (x+h)-arc_length g x)/h|) (N v) w hNorm hAbs)=> h hn.
rewrite (real_seminorm_scale hN.1) normrM !normfV.
have hb := @arc_length_distance_abs R [the metricType R of real_norm_metric_space hN]
  g hg (x+h) x.
have hi : 0<=`|h|^-1 by rewrite invr_ge0 normr_ge0.
have hs := ler_wpM2l hi hb.
by rewrite [X in _<=X]mulrC in hs.
Qed.

(** Source for [normed_bv_variation_derivative_ae]: supporting
    variation conclusion of Federer 2.9.22, pp. 167–168,
    extending 2.9.19(1), pp. 163–165. Given actual norm derivative
    existence almost everywhere, fine nearly maximal metric partitions
    remove the strict excess s'>N(g'). The reverse inequality follows
    from distance control. Reflexivity is needed for derivative
    existence elsewhere, not for this variation argument. *)
Theorem normed_bv_variation_derivative_ae (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : E,
    has_normed_curve_derivative N g x v /\ has_real_curve_derivative (arc_length g) x (N v) /\
    punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) (N v)].
Proof.
move=> hg hExists; have hm := lebesgue_scalar_is_measure R.
pose Bad := \bigcup_n metric_variation_defect_locus g n.
have hBad : lebesgue_scalar_measure Bad=0%E := metric_variation_defect_union_null hg.
have hGood : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` Bad).
  by rewrite /measure_almost_everywhere setCK.
have hs (a b : R) : a<=b -> arc_length g a<=arc_length g b :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg a b.
have hS := @monotone_real_derivative_exists_ae R (arc_length g) hs.
have hall := measure_almost_everywhere_and hm (measure_almost_everywhere_and hm hExists hS) hGood.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hall)=> x [[[v hG] [w [hw hDerS]]] hnBad].
have hlo := @normed_bv_derivative_variation_bound R E N hN g x w v hg hG hDerS hw.
have hup : w<=N v.
  rewrite leNgt; apply/negP=> hgap.
  have [n hn] := @normed_excess_arc_derivative_in_defect_locus R E N hN g x w v hG hDerS hgap.
  apply: hnBad; by exists n.
have heq : w=N v by apply: le_anti; rewrite hlo hup.
rewrite heq in hDerS.
exists v; split=> //; split=> //.
exact ((@metric_curve_variation_derivative_iff R [the metricType R of real_norm_metric_space hN]
  g x (N v) hg).1 hDerS).
Qed.

(** Source for [reflexive_bv_variation_derivative_ae]: direct
    norm differentiation and variation equality in Federer 2.9.22,
    pp. 167–168, extending 2.9.19(1), pp. 163–165. Combine
    the proved reflexive Banach norm derivative existence with the
    metric defect argument. All scalar dual derivative identities hold
    on the same conull set; no uncountable intersection is taken. *)
Theorem reflexive_bv_variation_derivative_ae (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : E,
    has_normed_curve_derivative N g x v /\ has_real_curve_derivative (arc_length g) x (N v) /\
    punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) (N v) /\
    forall alpha, has_real_curve_derivative (fun t => ed alpha (g t)) x (ed alpha v)].
Proof.
move=> hY ht hr hg.
have hNorm := @reflexive_bv_derivative_ae R E D B N hN ed DN hD eb BN hB tau g hY ht hr hg.
have hExists : measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v].
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ hNorm)=> x [v [hv _]]; by exists v.
have hVar := @normed_bv_variation_derivative_ae R E N hN g hg hExists.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hVar)=> x [v [hv [hs hlim]]].
exists v; split=> //; split=> //; split=> //.
exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv).
Qed.
