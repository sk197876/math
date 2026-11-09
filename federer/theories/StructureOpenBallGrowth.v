(** Federer (1969), 3.3.4, p. 291:
    compare the actual reference closed-ball
    quotients with the original unnormalized open-ball
    growth. Numerators remain arbitrary outer measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext
  MetricClosedBalls MetricDensities EuclideanBallVolume CoveringFamilyLaws
  NullBallLocus PositiveRightOrderLimit StructureDensityBallBounds
  StructureWeightedQuotient StructureRadiusPowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_open_ball_growth]:
    psi_v[B(z,t)] t^(-m), with the original
    open ball, in Federer 3.3.4, p. 291.
    Only positive t enter the later limits. *)
Definition structure_open_ball_growth (R:realType) (X:metricType R)
    m (psi:set X->\bar R) (x:X) (r:R): \bar R:=
  (psi [set y|(mdist x y<r)%R]*((r^-1)^+m)%:E)%E.

(** Source for [structure_open_ball_growth_nonnegative]:
    the actual unnormalized ball costs used in
    Federer 3.3.4, p. 291, are nonnegative
    at every positive radius, with infinite
    numerator mass permitted. *)
Lemma structure_open_ball_growth_nonnegative (R:realType) (X:metricType R)
    m (psi:set X->\bar R) (x:X) (r:R):
  is_measure psi ->0<r ->(0<=structure_open_ball_growth m psi x r)%E.
Proof.
move=>hPsi hr; apply:mule_ge0; first exact:measure_nonnegative hPsi _.
by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
Qed.

(** Source for [structure_open_ball_ratio_comparisons]:
    the density-based quotient replacement in Federer
    3.3.4, p. 291. Near zero, open-ball
    costs are bounded by 2 alpha(m) times
    the actual reference quotient, and that
    quotient is bounded by 2^m/(alpha(m)/2)
    times the original open-ball cost at 2r.
    No numerator regularity or finiteness is used. *)
Theorem structure_open_ball_ratio_comparisons (R:realType) (X:metricType R)
    m (phi psi:set X->\bar R) (x:X):
  is_derivation_measure phi ->is_measure psi ->
  ~measure_null_ball_points phi x ->
  positive_right_extended_order_limit (metric_ball_density m phi x) 1%E ->
  exists d:R,0<d /\ forall r,0<r<d ->
    (structure_open_ball_growth m psi x r<=
      (2*euclidean_unit_ball_volume R m)%:E*
        (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)))%E /\
    (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)<=
      ((2:R)^+m/(euclidean_unit_ball_volume R m/2))%:E*
        structure_open_ball_growth m psi x ((2*r)%R))%E.
Proof.
move=>hPhi hPsi hNo hDensity.
have hMu:=derivation_measure_law hPhi.
have [d [hd hBounds]]:=structure_density_one_ball_bounds hDensity.
exists d; split=>// r /andP [hr hrd].
have hrD:0<r<d by apply/andP.
have [hLower hUpper]:=hBounds r hrD.
have hPositive:=outside_null_ball_points_positive hMu hNo hr.
have hFinite:phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hMu _)).
  exact:(derivation_measure_bounded_finite hPhi (covering_closed_ball_bounded x (ltW hr))).
pose b:=fine (phi (metric_closed_ball x r)).
have hMass:phi (metric_closed_ball x r)=b%:E by rewrite /b fineK.
have hb:0<b by move:hPositive; rewrite hMass lte_fin.
have hbU:b<=(2*euclidean_unit_ball_volume R m)*r^+m.
  by move:hUpper; rewrite hMass lee_fin.
have hbL:(euclidean_unit_ball_volume R m/2)*r^+m<=b.
  apply:ltW; by move:hLower; rewrite hMass lte_fin.
have hAlpha:0<euclidean_unit_ball_volume R m:=(euclidean_unit_ball_volumeE R m).2.
split; rewrite /structure_open_ball_growth hMass.
- apply:structure_weighted_quotient_upper=>//.
  + exact:measure_nonnegative hPsi _.
  + apply:(measure_mono hPsi)=>y hy; exact:ltW hy.
  + by rewrite exprn_gt0 // invr_gt0.
  + exact:structure_radius_power_upper hr hbU.
- apply:structure_weighted_quotient_lower=>//.
  + exact:measure_nonnegative hPsi _.
  + apply:(measure_mono hPsi)=>y hy.
    have hr2:r<2*r by lra.
    exact:le_lt_trans hy hr2.
  + by rewrite exprn_gt0 // invr_gt0 mulr_gt0 // ltr0n.
  + apply:structure_radius_power_inverse_lower hr _ hbL.
    by rewrite divr_gt0 // ltr0n.
Qed.
