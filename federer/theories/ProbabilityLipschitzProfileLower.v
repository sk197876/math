(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: a common positive mass near a profile maximum
    gives a lower bound for every finite exponent norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric CoveringFamilyUP MeasureUP MeasureBasic
  PartialFunctionBasic MeasurableFunctionUP MeasureGauge MeasureLpNorm MeasureLpSuperlevelRoot RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_lipschitz_profile_norm_lower]: expanded
    support for the exponent infinity endpoint of Federer 3.2.45,
    p. 279. A normalized nonnegative profile attaining one has
    L^p norm at least r a^(1/p), if every delta-ball has mass
    at least a and L delta < 1-r. The existing superlevel-root
    bound from 2.4.17, p. 90, supplies the norm estimate. All
    geometric uniformity is stated separately and proved before
    applying this elementary measure-theoretic connection. *)
Theorem probability_lipschitz_profile_norm_lower (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hMu : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (L delta r a p : R) :
  mu setT = 1 -> (0 <= L)%R -> (0 < delta)%R -> (0 < r)%R -> (0 < a)%R ->
  (L*delta < 1-r)%R -> (1 <= p)%R ->
  (forall x, (0 <= f x)%R) ->
  (exists x, f x = 1%R) ->
  (forall x y, (`|f x-f y| <= L*mdist x y)%R) ->
  (forall x, a%:E <= mu (@metric_open_ball R X x delta)) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  ((r * real_power a (p^-1))%R)%:E <=
    measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f).
Proof.
move=> hTotal hL hDelta hR hA hGap hP hNonnegative [x0 hMax] hLipschitz hFloor hMeasurable.
pose A := partial_norm_superlevel (fun y : R => `|y|%R) (partial_function_total f) r%:E.
have hContain : @metric_open_ball R X x0 delta `<=` A.
  move=> y hY.
  have hDistance : (mdist x0 y < delta)%R := hY.
  have hBound := le_trans (ler_norm (f x0-f y))
    (le_trans (hLipschitz x0 y) (ler_wpM2l hL (ltW hDistance))).
  rewrite hMax in hBound.
  have hLarge : (r < f y)%R by lra.
  exists (f y); split=> //.
  change (is_true (r%:E < (`|f y|%R)%:E)).
  by rewrite (ger0_norm (hNonnegative y)) lte_fin.
have hLower : a%:E <= mu A := le_trans (hFloor x0)
  (@measure_mono R X mu hMu _ _ hContain).
have hUpper : mu A <= 1.
  have h := @measure_mono R X mu hMu A setT (subsetT A).
  by rewrite hTotal in h.
have hFinite : mu A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hMu A)).
  exact: le_lt_trans hUpper (ltry (1 : R)).
pose b : R := fine (mu A).
have hValue : mu A = b%:E := esym (fineK hFinite).
have hAB : (a <= b)%R by rewrite hValue lee_fin in hLower.
have hB : (0 <= b)%R := ltW (lt_le_trans hA hAB).
have hRoot := @measure_lp_superlevel_root_bound R X R^o
  (fun y : R => `|y|%R) (scalar_absolute_value_norm R) mu hMu p r b
  (partial_function_total f) hP hR hB hMeasurable hValue.
have hPPositive : (0 < p)%R := lt_le_trans ltr01 hP.
have hInverse : (0 < p^-1)%R by rewrite invr_gt0.
have hPower := @real_power_monotone R a b (p^-1)%R (ltW hA) hAB hInverse.
exact: le_trans (lee_tofin (ler_wpM2l (ltW hR) hPower)) hRoot.
Qed.
