(** Federer (1969), 2.9.19, pp. 163–165: finite differentiability and the
    two induced-measure alternatives of condition (2). The integral estimate
    is a separate remaining conclusion of the numbered theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  RealCurveDerivativeUP StieltjesImageMeasures StieltjesFiniteDerivates
  StieltjesDerivateComparisons RealBVVariationDerivative MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivates PartialFunctionUP ScalarIntervalDerivationContext LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_derivative_alternative]: direct finite algebra
    at the end of Federer 2.9.19's variation argument, pp. 164–165
    Nonnegative p,m with p-m=v and p+m<=|v| cannot both be positive. Thus
    either v=p and m=0, or v=-m and p=0. *)
Lemma nonnegative_derivative_alternative (R : realType) (p m v : R) :
  0<=p -> 0<=m -> p-m=v -> p+m<=`|v| ->
  (v=p /\ m=0) \/ (v= -m /\ p=0).
Proof.
move=> hp hm hpm hsum; case: (leP m p)=> hmp.
- have hnon : 0<=p-m by rewrite subr_ge0.
  rewrite -hpm (ger0_norm hnon) in hsum.
  have hm0 : m=0 by lra.
  left; split; first by rewrite -hpm hm0 subr0.
  exact hm0.
- have hnon : p-m<=0 by rewrite subr_le0; exact: ltW hmp.
  rewrite -hpm (ler0_norm hnon) opprB in hsum.
  have hp0 : p=0 by lra.
  right; split; first by rewrite -hpm hp0 sub0r.
  exact hp0.
Qed.

(** Source for [real_bv_derivative_alternative_ae]: direct finite
    differentiability and conditions (1),(2) in Federer 2.9.19, pp. 163–165
    On a common conull set, the two induced derivates p,m are finite
    nonnegative, g'=v, s'=|v|, p-m=v and p+m<=|v|. The scalar alternative
    proves exactly the printed cases, using actual partial derivate graphs
    and the two-sided signed variation limit. The temporary continuity-point
    restriction disappears by nullity of the curve's countable discontinuity
    set. *)
Theorem real_bv_derivative_alternative_ae (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : R,
    has_real_curve_derivative g x v /\
    punctured_real_limit (fun h => fine (signed_curve_variation
      (g : R -> real_line_metric R) x (x+h))/h) `|v| /\
    ((partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x v%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E) \/
     (partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x (-v)%:E /\
      partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
        psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E))].
Proof.
move=> hg hp; have hm := lebesgue_scalar_is_measure R.
have hAbs := @real_bv_absolute_variation_derivative_ae R g hg.
have hVals := @stieltjes_induced_derivates_finite_ae R g psip psim hg hp.
have hCont := @real_bv_continuity_ae R g hg.
have hPair := measure_almost_everywhere_and hm hAbs hVals.
have hAll := measure_almost_everywhere_and hm hPair hCont.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hAll).
move=> x [[[v [hG [hS hV]]] [p [m [hp0 [hm0 [hDp hDm]]]]]] hcx].
have [hpm hsum] := @stieltjes_derivate_comparisons_at_continuity_point R
  g psip psim x v `|v| p m hg hp hcx hG hS hDp hDm.
have hAlt := @nonnegative_derivative_alternative R p m v hp0 hm0 hpm hsum.
exists v; split; first exact hG.
split; first exact hV.
case: hAlt=> [[hv hmzero]|[hv hpzero]].
- left; split; first by rewrite hv.
  by rewrite hmzero in hDm.
- right; split; first by rewrite hv opprK.
  by rewrite hpzero in hDp.
Qed.
