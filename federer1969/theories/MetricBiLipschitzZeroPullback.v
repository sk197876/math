(** Federer (1969), 3.2.17, pp. 254–255:
    pull a zero-density exceptional subset of
    the parametrized image back to K. The
    inverse Lipschitz bound controls Hausdorff mass,
    and both radii use the same metric
    m-density normalization alpha(m)r^m. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import LipschitzUP MetricBiLipschitzUP MetricBiLipschitzHausdorff
  PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction MetricClosedBalls
  MetricDensities MetricDensityZeroPowerMass HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_bilipschitz_zero_density_pullback]:
    the local inverse measure comparison used
    to recover the full tangent plane in
    Federer 3.2.17, pp. 254–255. This
    intersection-definition form transfers an arbitrary
    full-density target set, instead of separately
    computing the volume of a directional cone. *)
Theorem metric_bilipschitz_zero_density_pullback (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (lambda : R) m a (A : set Y) :
  is_metric_bilipschitz_bound K f lambda -> 0<lambda -> K a ->
  partial_function_graph (metric_density m (measure_restrict
    (measure_restrict (@hausdorff_measure R Y m) (f @` K)) A)) (f a) 0%E ->
  partial_function_graph (metric_density m (measure_restrict
    (@hausdorff_measure R X m) (K `&` (f @^-1` A)))) a 0%E.
Proof.
move=> hB hLam ha hA.
pose mu := @hausdorff_measure R X m.
pose nu := measure_restrict (@hausdorff_measure R Y m) (f @` K).
have hm := @hausdorff_measure_is_measure R X m.
have hn := measure_restrict_is_measure (@hausdorff_measure_is_measure R Y m) (f @` K).
apply: (small_power_mass_metric_zero_density hm _)=> e he.
pose C := lambda^+(m+m).
have hC : 0<C by rewrite /C exprn_gt0.
have hc : 0<e/C by rewrite divr_gt0.
have [d [hd hSmall]] := metric_zero_density_small_power_mass hn hA hc.
exists (d/lambda); split; first by rewrite divr_gt0.
move=> r /andP [hr hrd].
have hrr : 0<lambda*r<=d.
  apply/andP; split; first exact: mulr_gt0 hLam hr.
  apply: ltW; move: hrd; by rewrite ltr_pdivlMr // mulrC.
pose B := (K `&` (f @^-1` A)) `&` metric_closed_ball a r.
have hBK : B `<=` K by move=> x hx; exact hx.1.1.
have hImage : f @` B `<=` (f @` K) `&` (A `&` metric_closed_ball (f a) (lambda*r)).
  move=> y [x [[hxK hxA] hxBall] <-]; split; first by exists x.
  split=> //; apply: (le_trans (hB.1.2 a x ha hxK) _).
  exact: (ler_wpM2l (ltW hLam) hxBall).
have hInv := (@metric_bilipschitz_hausdorff_bounds R X Y K f lambda a m B hB hBK).2.
have hMono := @measure_mono R Y (@hausdorff_measure R Y m)
  (@hausdorff_measure_is_measure R Y m) _ _ hImage.
have hMass := hSmall (lambda*r) hrr.
have hPow : (0<=(lambda^+m)%R%:E)%E by rewrite lee_fin exprn_ge0 // ltW.
have hscale := lee_wpmul2l hPow (le_trans hMono hMass).
apply: (le_trans hInv _).
apply: (le_trans hscale _); rewrite -EFinM lee_fin.
have hCore : lambda^+m*(e/C)*lambda^+m=e.
  rewrite [lambda^+m*(e/C)]mulrC -mulrA -exprD -/C.
  by rewrite divfK ?gt_eqF.
have hEq : lambda^+m*(e/C*(lambda*r)^+m)=e*r^+m.
  rewrite exprMn.
  have hAssoc : lambda^+m*(e/C*(lambda^+m*r^+m))=
      (lambda^+m*(e/C)*lambda^+m)*r^+m by ring.
  by rewrite hAssoc hCore.
by rewrite hEq.
Qed.
