(** Federer (1969), 2.10.2(1), p. 171: finite H^m(A) implies H^k(A)=0 for
    m<k. This proof treats the all nonnegative real degrees, allowing
    arbitrary sets and metric spaces; no measurability or separability is
    imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffDimensionGauge MetricDiameterUP MetricDiameter
  RealPowerDegreeComparison RealPower RealPowerContinuity MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasure
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleCutoffCost MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_finite_higher_degree_zero]: direct
    dimension-drop assertion of Federer 2.10.2(1), p. 171, for real m<k.
    Compare each fixed k-cutoff to arbitrarily small m-cutoffs, then use
    finiteness of the m-dimensional mass. *)
Theorem metric_real_power_finite_higher_degree_zero (R : realType) (X : metricType R)
    (u v m k : R) (hu : (0<u)%R) (hv : (0<v)%R)
    (hdegree : (0<=m)%R) (hmk : (m<k)%R) (A : set X) :
  @metric_real_power_measure R X u m A < +oo -> @metric_real_power_measure R X v k A = 0.
Proof.
move=> hf.
have hdiff : (0<k-m)%R by rewrite subr_gt0.
have hm := @metric_real_power_measure_specification R X u m.
have hk := @metric_real_power_measure_specification R X v k.
have ha0 := measure_nonnegative (@metric_real_power_measure_is_measure R X u m (ltW hu)) A.
case he: (@metric_real_power_measure R X u m A) ha0 hf=> [a| |] ha0 hf; last 2 first.
- by rewrite ltxx in hf.
- by [].
have ha : (0<=a)%R by move: ha0; rewrite lee_fin.
pose C : R := (v/u)%R.
have hC : (0<C)%R by rewrite /C divr_gt0.
apply/eqP; rewrite eq_le (measure_nonnegative (@metric_real_power_measure_is_measure R X v k (ltW hv))) andbT.
apply: (caratheodory_limit_least hk)=> tau nu htau hnu.
apply: (@extended_real_reciprocal_upper_bound R (nu A) 0)=> n.
pose e : R := (((n.+1)%:R)^-1)%R.
have hepos : (0<e)%R by rewrite /e invr_gt0 ltr0n.
pose c : R := (e/(a+1))%R.
have ha1 : (0<a+1)%R by lra.
have hc : (0<c)%R by rewrite /c divr_gt0.
have [j hj] := reciprocal_metric_cutoffs_cofinal htau.
pose b : R := (((j.+1)%:R)^-1)%R.
have hb : (0<b)%R by rewrite /b invr_gt0 ltr0n.
pose root : R := real_power (c/C) (k-m)^-1.
have hcC : (0<c/C)%R by rewrite divr_gt0.
have hroot : (0<root)%R := real_power_strictly_positive _ hcC.
pose delta : R := (Order.min b root)%R.
have hd : (0<delta)%R by rewrite /delta lt_min hb hroot.
have hdb : (delta<=b)%R.
  by rewrite /delta ge_min lexx.
have hdC : (delta<=root)%R by rewrite /delta ge_min lexx orbT.
have hdt : delta%:E<=tau := le_trans (lee_tofin hdb) hj.
pose phi := metric_scale_envelope (fun s : @nonempty_metric_sets R X => val s)
  (fun s => metric_real_diameter_cost u m (val s)) delta%:E.
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => metric_real_diameter_cost u m (val s)) delta%:E.
have hn_measure : is_measure nu.
  exact: metric_scale_envelope_is_measure hnu (fun s => metric_real_power_cost_nonnegative k _ (ltW hv)).
have hgen (s : @nonempty_metric_sets R X) : extended_metric_diameter (val s)<=delta%:E ->
    nu (val s)<=(C*real_power delta (k-m))%R%:E*metric_real_diameter_cost u m (val s).
  move=> hs.
  have hbound := @metric_scale_generator_bound R X (@nonempty_metric_sets R X)
    (fun s => val s) (fun s => metric_real_diameter_cost v k (val s)) tau nu s hnu
    (metric_real_power_cost_nonnegative k _ (ltW hv)) (le_trans hs hdt).
  apply: le_trans hbound _; rewrite /metric_real_diameter_cost.
  have hzero := metric_diameter_nonnegative (extended_metric_diameter_specification (val s)).
  case: (extended_metric_diameter (val s)) hzero hs=> [d| |] hzero hs; last 2 first.
  + by rewrite leye_eq in hs.
  + by [].
  have hd0 : (0<=d)%R by move: hzero; rewrite lee_fin.
  have hdd : (d<=delta)%R by move: hs; rewrite lee_fin.
  exact: @metric_real_power_higher_degree_cost R u v m k d delta hu hv hdegree hmk hd0 hdd.
have hcd : (0<C*real_power delta (k-m))%R by rewrite mulr_gt0 //; exact:real_power_strictly_positive _ hd.
have hbound := @measure_bounded_by_scaled_metric_envelope R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => metric_real_diameter_cost u m (val s)) delta%:E phi nu (C*real_power delta (k-m))%R
  hphi hn_measure hcd hgen A.
have hup := @caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => metric_real_diameter_cost u m (val s)) _ hm A delta%:E phi hd hphi.
have hbound' := le_trans hbound (lee_wpmul2l (lee_tofin (ltW hcd)) hup).
rewrite he -EFinM in hbound'.
have hCdelta : (C*real_power delta (k-m)<=c)%R.
  have hPower := real_power_monotone (ltW hd) hdC hdiff.
  have hRoot : (real_power root (k-m)=c/C)%R.
    rewrite /root; exact:real_power_inverse_power (ltW hcC) hdiff.
  have hh := ler_wpM2l (ltW hC) hPower.
  have hEq : (C*(c/C)=c)%R by rewrite mulrC divfK ?gt_eqF.
  by rewrite hRoot hEq in hh.
have hca : (c*a<=e)%R.
  have haa1 : (a<=a+1)%R by rewrite lerDl ler01.
  have hh := ler_wpM2l (ltW hc) haa1.
  by rewrite /c divfK ?gt_eqF in hh.
apply: le_trans hbound' _; rewrite add0r lee_fin.
exact: le_trans (ler_wpM2r ha hCdelta) hca.
Qed.
