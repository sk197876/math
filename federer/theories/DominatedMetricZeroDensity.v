(** Federer (1969), 3.3.18, p. 301: transfer zero metric
    density through independent finite measure comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MetricDensities MetricDensityNumericalBounds
  MetricDensityZero MetricClosedBalls EuclideanBallVolume PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_metric_zero_density]: the measure-comparison
    step in Federer 3.3.18, p. 301. Domination by a nonnegative
    FINITE constant transfers ordinary zero m-density. The measures
    and all original positive radii remain; no finite ball masses or
    positive density are assumed. *)
Theorem dominated_metric_zero_density (R:realType) (X:metricType R) m
    (mu nu:set X->\bar R) (a:X) (c:R):
  is_measure mu ->is_measure nu ->(0<=c)%R ->
  (forall A,mu A<=c%:E*nu A) ->
  partial_function_graph (metric_density m nu) a 0 ->
  partial_function_graph (metric_density m mu) a 0.
Proof.
move=>hMu hNu hC hBound hZero.
apply:(@metric_density_zero_iff_upper_zero R X m mu a hMu).2.
apply:(@metric_upper_density_zero_iff_small R X m mu a hMu).2=>e he.
have hCP:(0<c+1)%R by lra.
pose q:=(e/(c+1))%R.
have hQ:(0<q)%R by rewrite /q divr_gt0.
have hUpper:=(@metric_density_zero_iff_upper_zero R X m nu a hNu).1 hZero.
have [d [hd hSmall]]:=(@metric_upper_density_zero_iff_small R X m nu a hNu).1 hUpper q hQ.
exists d; split; first exact:hd.
move=>r /andP[hr hrd].
have hRadius:(0<r<d)%R by apply/andP; split.
have hDen:(0<=((euclidean_unit_ball_volume R m*r^+m)%:E)^-1)%E.
  rewrite inve_ge0 lee_fin; exact:ltW (metric_ball_density_denominator_positive m hr).
have hMass:=lee_wpmul2r hDen (hBound (MetricClosedBalls.metric_closed_ball a r)).
rewrite -muleA in hMass.
change (is_true (metric_ball_density m mu a r<=c%:E*metric_ball_density m nu a r)%E) in hMass.
apply:le_trans hMass _.
have hCE:(0<=c%:E)%E by rewrite lee_fin.
apply:le_trans (lee_wpmul2l hCE (hSmall r hRadius)) _.
rewrite -EFinM lee_fin.
have hLe:(c<=c+1)%R by lra.
have hScaled:=ler_wpM2r (ltW hQ) hLe.
have hCancel:((c+1)*q=e)%R by rewrite mulrC /q divfK ?gt_eqF.
by rewrite hCancel in hScaled.
Qed.
