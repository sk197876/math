(** Federer (1969), 2.10.2(1), p. 171: finite H^m(A) implies H^k(A)=0 for
    m<k. This proof treats the printed nonnegative integer degrees, allowing
    arbitrary sets and metric spaces; no measurability or separability is
    imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffDimensionGauge MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleCutoffCost MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_finite_mass_higher_degree_zero]: direct
    dimension-drop assertion of Federer 2.10.2(1), p. 171, for integer m<k.
    Compare each fixed k-cutoff to arbitrarily small m-cutoffs, then use
    finiteness of the m-dimensional mass. *)
Theorem hausdorff_finite_mass_higher_degree_zero (R : realType) (X : metricType R)
    (m k : nat) (A : set X) : (m<k)%N ->
  @hausdorff_measure R X m A < +oo -> @hausdorff_measure R X k A = 0.
Proof.
move=> hmk hf.
have hm := @hausdorff_measure_specification R X m.
have hk := @hausdorff_measure_specification R X k.
have ha0 := measure_nonnegative (@hausdorff_measure_is_measure R X m) A.
case he: (@hausdorff_measure R X m A) ha0 hf=> [a| |] ha0 hf; last 2 first.
- by rewrite ltxx in hf.
- by [].
have ha : (0<=a)%R by move: ha0; rewrite lee_fin.
pose C : R := (hausdorff_normalisation R k/hausdorff_normalisation R m)%R.
have hC : (0<C)%R by rewrite /C divr_gt0 //; exact: hausdorff_normalisation_positive.
apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R X k)) andbT.
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
pose delta : R := (Order.min 1 (Order.min b (c/C)))%R.
have hd : (0<delta)%R by rewrite /delta !lt_min ltr01 hb divr_gt0.
have hd1 : (delta<=1)%R by rewrite /delta ge_min lexx.
have hdb : (delta<=b)%R.
  rewrite /delta !ge_min; apply/orP; right; apply/orP; left; exact: lexx.
have hdC : (delta<=c/C)%R.
  rewrite /delta !ge_min; apply/orP; right; apply/orP; right; exact: lexx.
have hdt : delta%:E<=tau := le_trans (lee_tofin hdb) hj.
pose phi := metric_scale_envelope (fun s : @nonempty_metric_sets R X => val s)
  (fun s => hausdorff_diameter_cost m (val s)) delta%:E.
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => hausdorff_diameter_cost m (val s)) delta%:E.
have hn_measure : is_measure nu.
  exact: metric_scale_envelope_is_measure hnu (fun s => hausdorff_diameter_cost_nonnegative k (val s)).
have hgen (s : @nonempty_metric_sets R X) : extended_metric_diameter (val s)<=delta%:E ->
    nu (val s)<=(C*delta)%R%:E*hausdorff_diameter_cost m (val s).
  move=> hs.
  have hbound := @metric_scale_generator_bound R X (@nonempty_metric_sets R X)
    (fun s => val s) (fun s => hausdorff_diameter_cost k (val s)) tau nu s hnu
    (hausdorff_diameter_cost_nonnegative k (val s)) (le_trans hs hdt).
  apply: le_trans hbound _; rewrite /hausdorff_diameter_cost.
  have hzero := metric_diameter_nonnegative (extended_metric_diameter_specification (val s)).
  case: (extended_metric_diameter (val s)) hzero hs=> [d| |] hzero hs; last 2 first.
  + by rewrite leye_eq in hs.
  + by [].
  have hd0 : (0<=d)%R by move: hzero; rewrite lee_fin.
  have hdd : (d<=delta)%R by move: hs; rewrite lee_fin.
  exact: hausdorff_higher_degree_gauge_bound hmk hd0 hdd hd1.
have hcd : (0<C*delta)%R by rewrite mulr_gt0.
have hbound := @measure_bounded_by_scaled_metric_envelope R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => hausdorff_diameter_cost m (val s)) delta%:E phi nu (C*delta)%R
  hphi hn_measure hcd hgen A.
have hup := @caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun s => val s) (fun s => hausdorff_diameter_cost m (val s)) _ hm A delta%:E phi hd hphi.
have hbound' := le_trans hbound (lee_wpmul2l (lee_tofin (ltW hcd)) hup).
rewrite he -EFinM in hbound'.
have hCdelta : (C*delta<=c)%R.
  have hh := ler_wpM2l (ltW hC) hdC.
  by rewrite mulrCA mulfV ?gt_eqF // mulr1 in hh.
have hca : (c*a<=e)%R.
  have haa1 : (a<=a+1)%R by rewrite lerDl ler01.
  have hh := ler_wpM2l (ltW hc) haa1.
  by rewrite /c divfK ?gt_eqF in hh.
apply: le_trans hbound' _; rewrite add0r lee_fin.
exact: le_trans (ler_wpM2r ha hCdelta) hca.
Qed.
