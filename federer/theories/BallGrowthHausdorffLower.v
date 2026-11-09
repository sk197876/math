(** Federer (1969), 3.4.4, p. 318: compare
    actual real-degree product probabilities with Hausdorff measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import MeasureUP MeasureBasic FiniteMeasureScaling BallGrowthProbabilityUP
  MetricClosedBalls MetricDiameterUP MetricDiameter MetricRealPowerCost MetricRealPowerMeasure
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleMeasureBound CaratheodoryLimitUP HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ball_growth_probability_power_measure_lower]: the
    positive real-degree image mass in 3.4.4, p. 318,
    expanding its cited product lower-bound argument. Every
    original generator lies in a ball of its own diameter.
    The scaled probability is therefore below the actual
    diameter-power envelope at cutoff one, hence below its
    Caratheodory limit. The zero-diameter case remains included. *)
Theorem ball_growth_probability_power_measure_lower (R:realType) (X:metricType R)
    (A:set X) (K p b:R) (mu:set X->\bar R):
  is_ball_growth_probability A K p mu ->(0<b)%R ->
  ((b/K)%R%:E<=@metric_real_power_measure R X b p A)%E.
Proof.
move=>hMu hb.
have hK:=ball_growth_coefficient_positive hMu.
have hScale:(0<b/K)%R by rewrite divr_gt0.
pose nu:=fun T:set X=>(b/K)%R%:E*mu T.
have hNu:is_measure nu:=finite_scale_is_measure (ball_growth_measure hMu) (ltW hScale).
have hMass:nu A=(b/K)%R%:E by rewrite /nu (ball_growth_original_source_mass hMu) mule1.
pose xi:=@metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b p (val S)) 1.
have hXi:=@metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b p (val S)) 1.
have hGenerator (T:nonempty_metric_sets X):extended_metric_diameter (val T)<=1 ->
    nu (val T)<=metric_real_diameter_cost b p (val T).
  move=>hDiameter.
  have hNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification (val T)).
  case hD:(extended_metric_diameter (val T)) hNonnegative hDiameter=>[d| |] hd hd1;last 2 first.
  - by rewrite leye_eq in hd1.
  - by [].
  have hd0:(0<=d)%R by move:hd;rewrite lee_fin.
  have [x hx]:val T !=set0:=set_valP T.
  have hCover:val T `<=` metric_closed_ball x d.
    move=>y hy.
    have h:=metric_diameter_upper (extended_metric_diameter_specification (val T)) hx hy.
    by rewrite hD lee_fin in h.
  have hLocal:=le_trans (measure_mono (ball_growth_measure hMu) hCover)
    (ball_growth_bound hMu x hd0).
  have hBound:=lee_wpmul2l (lee_tofin (ltW hScale)) hLocal.
  have hCancel:((b/K)*(K*RealPower.real_power d p)=b*RealPower.real_power d p)%R.
    by rewrite mulrA divfK ?gt_eqF.
  rewrite /nu /metric_real_diameter_cost hD metric_real_power_cost_finite.
  by rewrite -EFinM hCancel in hBound.
have hBound:=@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b p (val S)) 1 xi nu hXi hNu hGenerator A.
rewrite hMass in hBound.
apply:le_trans hBound _.
exact:(@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>metric_real_diameter_cost b p (val S)) _
  (@metric_real_power_measure_specification R X b p) A 1 xi (ltac:(by [])) hXi).
Qed.
