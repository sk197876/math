(** Federer 2.10.42, p. 201, in every nonnegative real degree.
    Reuse Jung's original minimum ball and the existing weighted covering
    comparison. The actual Gamma-normalized measures occur throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric FiniteCoordinates
  RealPower RealPowerContinuity RealPowerCoverVariants RealPowerSphericalComparison
  RealPowerSingletonBound RealHausdorffNormalisation RealHausdorffMeasure
  RealHausdorffMeasureLaws
  HausdorffLengthUP HausdorffMeasureUP MetricRealPowerCost MetricDiameterUP
  MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleWeightedBound MetricScaleCutoffCost CaratheodoryLimitUP
  CaratheodoryBorelRegular MeasureUP MeasureBasic ExtendedRealOrderTopology
  JungConstant RealPowerJungCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_euclidean_real_spherical_jung_comparison]:
    direct real-degree comparison of Federer 2.10.42, p. 201, in
    positive ambient dimension. Replace each small Hausdorff generator
    by its proved Jung ball, apply the existing weighted envelope
    comparison, and pass to the original covering supremum. No target
    measurability or finite-mass premise is added. *)
Theorem positive_euclidean_real_spherical_jung_comparison (R : realType) n
    (p : R) (hp : (0<=p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
    @real_spherical_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)] p hp A<=
    (real_power (@jung_factor R n.+1) p)%:E * @real_hausdorff_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)] p hp A.
Proof.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)].
pose a := real_hausdorff_normalisation hp.
have ha : (0<a)%R := real_hausdorff_normalisation_positive hp.
pose q := @jung_factor R n.+1.
have hq : (0<q)%R.
  by rewrite /q /jung_factor sqrtr_gt0 divr_gt0 ?mulr_gt0 ?ltr0n.
have hden : (0<q+1)%R by lra.
pose C := real_power q p.
have hC : (0<C)%R := @real_power_strictly_positive R q p hq.
have hCE : 0<=C%:E by rewrite lee_fin; exact: ltW hC.
apply: (caratheodory_limit_least (@real_spherical_measure_specification R X p hp)) => tau xi htau hxi.
have [k hkt] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((k.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose s : R := (t/(q+1))%R.
have hs : (0<s)%R by rewrite /s divr_gt0.
pose psi := metric_scale_envelope (fun j : @positive_closed_metric_balls R X => val j)
  (fun j => metric_real_diameter_cost a p (val j)) t%:E.
have hpsi := @metric_scale_envelope_specification R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) t%:E.
have hpsi_measure : is_measure psi.
  apply: (@metric_scale_envelope_measure R X (@positive_closed_metric_balls R X)
    (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) t%:E).
  move=> j; exact: metric_real_diameter_cost_ge0 (ltW ha).
pose phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
  (fun j => metric_real_diameter_cost a p (val j)) s%:E.
have hphi := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) s%:E.
have hgen (j : @nonempty_metric_sets R X) : extended_metric_diameter (val j)<=s%:E ->
    psi (val j)<=C%:E*metric_real_diameter_cost a p (val j).
  move=> hj.
  have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  case he : (extended_metric_diameter (val j)) h0 hj => [d| |] h0 hj; last 2 first.
  - by rewrite leye_eq in hj.
  - by [].
  have hd : (0<=d)%R by move: h0; rewrite lee_fin.
  have hds : (d<=s)%R by move: hj; rewrite lee_fin.
  have hmul : (q*d<=q*s)%R := ler_wpM2l (ltW hq) hds.
  have heq : (s*(q+1)=t)%R by rewrite /s divfK // gt_eqF.
  have hcap : (q*d<t)%R by nra.
  have hdi : extended_metric_diameter (val j)<=d%:E by rewrite he.
  have hb := @real_power_jung_spherical_cutoff_bound R n.+1 a p ha hp
    psi (val j) d t hpsi (set_valP j) hd hcap hdi.
  by rewrite /metric_real_diameter_cost he.
have hb := @measure_bounded_by_scaled_metric_envelope R X (@nonempty_metric_sets R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) s%:E
  phi psi C hphi hpsi_measure hC hgen A.
have hup : phi A<=@real_hausdorff_measure R X p hp A.
  apply: (@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => metric_real_diameter_cost a p (val j)) _
    (@real_hausdorff_measure_specification R X p hp) A s%:E phi _ hphi).
  by rewrite lte_fin.
have hxiA := @metric_scale_envelope_antitone_cutoff R X (@positive_closed_metric_balls R X)
  (fun j => val j) (fun j => metric_real_diameter_cost a p (val j))
  t%:E tau psi xi hpsi hxi hkt A.
exact: (le_trans hxiA (le_trans hb (lee_wpmul2l hCE hup))).
Qed.

(** Source for [real_jung_power_coefficient]: supporting exact form
    of the coefficient in Federer 2.10.42, p. 201. The real power of
    sqrt(2n/(n+1)) equals the printed (2n/(n+1))^(p/2), including both
    zero degree and zero ambient dimension. Reuse the proved real-power
    square-root law. *)
Lemma real_jung_power_coefficient (R : realType) n (p : R) :
    (0<=p)%R ->
    real_power (@jung_factor R n) p=
      real_power (2*n%:R/n.+1%:R)%R (p/2)%R.
Proof.
move=> hp.
case: (eqVneq p 0%R)=> [he|hne].
- by rewrite he mul0r !real_power_zero_exponent.
have hpp : (0<p)%R by rewrite lt_def hne hp.
have hs := @real_power_square_half R (@jung_factor R n) p
  (@jung_factor_nonnegative R n) hpp.
have hbase : (0<=2*n%:R/n.+1%:R :> R)%R.
  by rewrite divr_ge0 ?mulr_ge0 ?ler0n.
by rewrite /jung_factor sqr_sqrtr // in hs; symmetry.
Qed.

(** Source for [federer_2_10_42_real_degree]: direct original comparison
    of Federer 2.10.42, p. 201, with the printed coefficient and every
    nonnegative real degree. The actual Gamma-normalized spherical and
    Hausdorff measures are used on every original subset. The zero
    ambient space and the 0^0=1 convention are retained. *)
Theorem federer_2_10_42_real_degree (R : realType) n
    (p : R) (hp : (0<=p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
    @real_spherical_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp A<=
    (real_power (2*n%:R/n.+1%:R)%R (p/2)%R)%:E * @real_hausdorff_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp A.
Proof.
rewrite -(@real_jung_power_coefficient R n p hp).
case: n A=> [|n] A; last exact: positive_euclidean_real_spherical_jung_comparison.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)].
have hS := @real_spherical_le_double_hausdorff R X p hp A.
case: (eqVneq p 0%R)=> [he|hne].
- have htwo : real_power 2%R p = 1%R by rewrite he real_power_zero_exponent.
  have hq : real_power (@jung_factor R 0) p = 1%R by rewrite he real_power_zero_exponent.
  rewrite hq mul1e; by rewrite htwo mul1e in hS.
- have hbound := @real_power_singleton_bound R X
    (real_hausdorff_normalisation hp) p (@real_hausdorff_measure R X p hp) (0%R : X)
    (@real_hausdorff_measure_specification R X p hp)
    (ltW (real_hausdorff_normalisation_positive hp)).
  rewrite real_power_zero_base // mulr0 in hbound.
  have hA : A `<=` [set (0%R : X)] by move=> x hx; exact: coordinate_zero.
  have hMass := le_trans (@measure_mono R X (@real_hausdorff_measure R X p hp)
    (@real_hausdorff_measure_is_measure R X p hp) A [set (0%R : X)] hA) hbound.
  have hzero : @real_hausdorff_measure R X p hp A=0.
    apply/eqP; rewrite eq_le hMass /=.
    exact: (@measure_nonnegative R X _ (@real_hausdorff_measure_is_measure R X p hp) A).
  rewrite hzero mule0 in hS *.
  by rewrite mule0; exact hS.
Qed.
