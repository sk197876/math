(** Federer (1969), 3.2.36, p. 273: actual evaluation of every
    weighted radius term, using the ball-section profile and polar formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBallVolume
  EuclideanBallSectionProfile BallSectionScalarIntegral BallSectionRadialGraph PolarSphereFormula
  RadialSphereIntegral ScalarPositiveCutoffIntegral LebesgueScalarMeasure MeasureIntegralUP
  MeasureIntegralUniqueness MeasureSubsetIntegral PartialFunctionUP SummableRealFunctionUP
  RealOpenIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_radial_section_integral]: the normalized
    radial coefficient calculation in Federer 3.2.36, p. 273:
    the integral of xi alpha(xi) alpha(eta) s^(xi-1)
    (r^2-s^2)^(eta/2) over 0<s<r equals
    alpha(xi+eta) r^(xi+eta), for every xi>0 and eta>=0.
    This expands the printed appeal to 3.2.13 through the already proved
    actual ball-section integral of 2.10.27, p. 191. No intrinsic-volume
    product identity, unproved beta value or new global witness is used.
    The nonzero endpoint when eta=0 is removed only by scalar nullity. *)
Theorem weighted_radial_section_integral (R:realType) m k (r:R):
  (0<m)%N ->0<r ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (real_total_integrand (fun s:R=>m%:R*euclidean_unit_ball_volume R m*
      euclidean_unit_ball_volume R k*s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k))
    (euclidean_unit_ball_volume R (m+k)*r^+(m+k))%R%:E.
Proof.
move=>hm hr.
pose hr0:=ltW hr.
pose g:=fun y=>fine (@euclidean_ball_section_profile R m k 0 r hr0 y).
have hBall:=@ball_section_scalar_integral R m k 0 r hr0.
have [a [hSource hPolar]]:=@polar_sphere_integral_formula R m g hm (ex_intro _ _ hBall).
have hA:=measure_integral_unique hSource hBall.
rewrite hA addnC in hPolar.
apply:(@scalar_positive_cutoff_integral R
  (@radial_sphere_integral R m (real_total_integrand g))
  (fun s:R=>m%:R*euclidean_unit_ball_volume R m*euclidean_unit_ball_volume R k*
    s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k) r _ _ _ hPolar).
- move=>s hs hsr; apply/(@ball_section_radial_graph R m k r s hr0 _ hm hs).
  by rewrite (ltW hsr).
- move=>s hrs; have hs:=lt_trans hr hrs.
  apply/(@ball_section_radial_graph R m k r s hr0 _ hm hs).
  by rewrite leNgt hrs.
Qed.
