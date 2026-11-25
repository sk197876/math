(** The valid finite-exponent estimate supporting Federer (1969),
    3.2.45, p. 279. Reuse the logarithmic convexity of
    2.4.17 and the corrected secant bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasureExponentDomain MeasureReciprocalInterval ReciprocalExponent ProbabilityExponentMonotone
  ProbabilityUnitProfileNormBounds MeasureLogarithmicConvexity ConvexReciprocalSecant
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_unit_profile_reciprocal_secant]:
    corrected supporting estimate for Federer 3.2.45, p. 279.
    A positive common bound d on the exponent-one norm gives
    norm_(1/u) <= exp((-log d)(v-u)/v) norm_(1/v),
    for 0<=u<v<=1. The denominator v is retained; this
    bound is used only for continuity at positive reciprocal
    exponents. No assertion of a uniform modulus at zero
    follows from this secant estimate. *)
Theorem probability_unit_profile_reciprocal_secant (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hMu : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) (d u v : R) :
  mu setT = 1 -> (0 < d)%R -> (forall x, (`|f x| <= 1)%R) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  d%:E <= measure_exponent_norm mu (partial_function_total f) 1 ->
  (0 <= u)%R -> (u < v)%R -> (v <= 1)%R ->
  measure_reciprocal_exponent_norm mu (partial_function_total f) u <=
    (@RealExponential.exponential R
      ((- RealExponential.logarithm d) * (v-u)/v)%R)%:E *
    measure_reciprocal_exponent_norm mu (partial_function_total f) v.
Proof.
move=> hProbability hD hUnit hF hLower hU hUV hV1.
pose N := measure_reciprocal_exponent_norm mu (partial_function_total f).
pose h := measure_reciprocal_log_norm mu (partial_function_total f).
pose C := (- RealExponential.logarithm d)%R.
have hDomain := @probability_unit_profile_reciprocal_domain R X mu hMu f d
  hProbability hD hUnit hF hLower.
have hBounds (x : R) (hx : (0 <= x <= 1)%R) : (0 < fine (N x))%R /\
    N x = (fine (N x))%:E /\ (fine (N x) <= 1)%R.
  have /andP[hx0 hx1] := hx.
  have [hLo hHi] := @probability_unit_profile_norm_bounds R X mu hMu f d
    hProbability hD hUnit hF hLower _
    (@reciprocal_lebesgue_exponent_domain R x hx0 hx1).
  rewrite -measure_reciprocal_exponent_normE in hLo hHi.
  have hPositive : 0 < N x := lt_le_trans (lte_tofin hD) hLo.
  have hFinite : N x \is a fin_num by rewrite (ge0_fin_numE (ltW hPositive)); exact: le_lt_trans hHi (ltry 1%R).
  have hValue : N x = (fine (N x))%:E by rewrite fineK.
  have hScalarPositive : (0 < fine (N x))%R.
    by move: hPositive; rewrite hValue lte_fin.
  have hScalarUpper : (fine (N x) <= 1)%R.
    change (is_true (N x <= (1%R)%:E)) in hHi.
    by rewrite hValue lee_fin in hHi.
  exact: (conj hScalarPositive (conj hValue hScalarUpper)).
have hConvex := @measure_reciprocal_log_norm_convex R X mu hMu (partial_function_total f) hF.
rewrite hDomain in hConvex.
have hMono (x y : R) (hx : (0 <= x)%R) (hxy : (x <= y)%R) (hy : (y <= 1)%R) : (h y <= h x)%R.
  have hx1 := le_trans hxy hy.
  have hy0 := le_trans hx hxy.
  have hxI : (0 <= x <= 1)%R by apply/andP; split.
  have hyI : (0 <= y <= 1)%R by apply/andP; split.
  have hNorm := @probability_measure_exponent_norm_monotone R X mu hMu _
    (reciprocal_lebesgue_exponent y) (reciprocal_lebesgue_exponent x)
    hProbability (@reciprocal_lebesgue_exponent_domain R y hy0 hy)
    (@reciprocal_lebesgue_exponent_antitone R x y hx hxy) hF.
  rewrite -!measure_reciprocal_exponent_normE in hNorm.
  change (is_true (N y <= N x)) in hNorm.
  rewrite (hBounds x hxI).2.1 (hBounds y hyI).2.1 lee_fin in hNorm.
  rewrite /h /measure_reciprocal_log_norm.
  by rewrite real_logarithm_order; [exact hNorm|exact: (hBounds y hyI).1|exact: (hBounds x hxI).1].
have h0 : (0 <= (0 : R) <= 1)%R by rewrite lexx ler01.
have h1 : (0 <= (1 : R) <= 1)%R by rewrite lexx ler01.
Close Scope ereal_scope.
have hZero : (h 0 <= 0)%R.
  have hLog : (RealExponential.logarithm (fine (N 0%R)) <= RealExponential.logarithm (1 : R))%R.
    rewrite (@real_logarithm_order R (fine (N 0%R)) 1%R (hBounds (0 : R) h0).1 (@ltr01 R)).
    exact: (hBounds (0 : R) h0).2.2.
  by rewrite real_logarithm_one in hLog.
have hOne : (RealExponential.logarithm d <= h 1)%R.
  have hLo := hLower.
  have hAtOne : N 1 = measure_exponent_norm mu (partial_function_total f) 1.
    by rewrite /N /measure_reciprocal_exponent_norm oner_eq0 invr1.
  rewrite -hAtOne (hBounds (1 : R) h1).2.1 lee_fin in hLo.
  change (is_true ((RealExponential.logarithm d <= RealExponential.logarithm (fine (N 1%R)))%R)).
  by rewrite (@real_logarithm_order R d (fine (N 1%R)) hD (hBounds (1 : R) h1).1).
have hRange : (h 0-h 1 <= C)%R by rewrite /C; lra.
have [_ hSecant] := @convex_nonincreasing_reciprocal_secant R h C hConvex hMono hRange u v hU hUV hV1.
have hUI : (0 <= u <= 1)%R by apply/andP; split=> //; exact: le_trans (ltW hUV) hV1.
have hVI : (0 <= v <= 1)%R by apply/andP; split=> //; exact: le_trans hU (ltW hUV).
have hAdd : (h u <= C*(v-u)/v+h v)%R by lra.
have hExp : (RealExponential.exponential (h u) <= RealExponential.exponential (C*(v-u)/v+h v))%R.
  by rewrite real_exponential_order.
rewrite (real_exponential_add (@RealExponential.laws R)) /h /measure_reciprocal_log_norm
  (real_exponential_logarithm (@RealExponential.laws R) (hBounds u hUI).1)
  (real_exponential_logarithm (@RealExponential.laws R) (hBounds v hVI).1) in hExp.
Open Scope ereal_scope.
change (is_true (N u <= (@RealExponential.exponential R (C*(v-u)/v)%R)%:E * N v)).
rewrite (hBounds u hUI).2.1 (hBounds v hVI).2.1 -EFinM lee_fin.
exact hExp.
Qed.
