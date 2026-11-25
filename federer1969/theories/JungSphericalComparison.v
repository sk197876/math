(** Federer (1969), 2.10.42, printed p. 201: spherical measure is bounded by
    Jung's diameter factor to power m times Hausdorff measure. Compare
    independent cutoff infima before taking the final spherical supremum.
    The present interface uses natural degrees, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleEnvelopeLaws MetricScaleMeasureBound CaratheodoryLimitUP
  CaratheodoryBorelRegular MeasureUP FiniteMeasureScaling ExtendedRealOrderTopology
  JungConstant JungSphericalCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_euclidean_spherical_jung_comparison]: direct
    natural-degree comparison of 2.10.42, p. 201,
    in positive ambient dimension. The target is
    arbitrary and either measure may be infinite.
    Source cutoff t/(q+1) keeps the containing-ball
    diameter strictly below spherical cutoff t, where
    q=sqrt(2n/(n+1)). No measurable-target premise is added. *)
Theorem positive_euclidean_spherical_jung_comparison (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)] m A<=
  ((@jung_factor R n.+1)^+m)%:E*@hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)] m A.
Proof.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)].
have hm := @hausdorff_measure_specification R X m.
have hn := @spherical_measure_specification R X m.
pose q : R := @jung_factor R n.+1.
have hq : (0<q)%R.
  by rewrite /q /jung_factor sqrtr_gt0 divr_gt0 ?mulr_gt0 ?ltr0n.
have hden : (0<q+1)%R by lra.
pose c : R := (q^+m)%R.
have hc : (0<c)%R by rewrite /c exprn_gt0.
have hci : (0<=c^-1)%R by rewrite invr_ge0; exact: ltW hc.
have hcE : 0<=c%:E by rewrite lee_fin; exact: ltW hc.
have hciE : 0<=((c^-1)%R)%:E by rewrite lee_fin.
apply: (caratheodory_limit_least hn)=> tau xi htau hxi.
have [k hkt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((k.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose s : R := (t/(q+1))%R.
have hs : (0<s)%R by rewrite /s divr_gt0.
pose psi := metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
  (fun j=>hausdorff_diameter_cost m (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@positive_closed_metric_balls R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) t%:E.
have hpsi_measure : is_measure psi := @metric_scale_envelope_measure R X (@positive_closed_metric_balls R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) t%:E
  (fun j=>hausdorff_diameter_cost_nonnegative m (val j)).
pose phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
  (fun j=>hausdorff_diameter_cost m (val j)) s%:E.
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) s%:E.
have hgen (j : @nonempty_metric_sets R X) : extended_metric_diameter (val j)<=s%:E ->
    ((c^-1)%R)%:E*psi (val j)<=hausdorff_diameter_cost m (val j).
  move=> hj; have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  case he: (extended_metric_diameter (val j)) h0 hj=> [d| |] h0 hj; last 2 first.
  - by rewrite leye_eq in hj.
  - by [].
  have hd : (0<=d)%R by move: h0; rewrite lee_fin.
  have hds : (d<=s)%R by move: hj; rewrite lee_fin.
  have hmul : (q*d<=q*s)%R := ler_wpM2l (ltW hq) hds.
  have heq : (s*(q+1)=t)%R by rewrite /s divfK // gt_eqF.
  have hcap : (q*d<t)%R by nra.
  have hdi : extended_metric_diameter (val j)<=d%:E by rewrite he.
  have hb := @jung_spherical_cutoff_generator_bound R n.+1 m psi (val j) d t
    hpsi (set_valP j) hd hcap hdi.
  have hh := lee_wpmul2l hciE hb.
  rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hh.
  by rewrite /hausdorff_diameter_cost he.
have hb := @measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) s%:E
  phi (fun B=>((c^-1)%R)%:E*psi B) hphi (finite_scale_is_measure hpsi_measure hci) hgen A.
have hup : phi A<=@hausdorff_measure R X m A.
  apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) _ hm A s%:E phi _ hphi).
  by rewrite lte_fin.
have hh := lee_wpmul2l hcE (le_trans hb hup).
rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hh.
apply: le_trans _ hh.
exact (@metric_scale_envelope_antitone_cutoff R X (@positive_closed_metric_balls R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) t%:E tau psi xi hpsi hxi hkt A).
Qed.
