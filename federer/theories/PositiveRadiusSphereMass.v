(** Federer (1969), 3.2.36, p. 273: the actual positive-radius sphere mass
    normalizes the radial integral using 3.2.13, p. 250. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HausdorffMeasure SphereDilationMeasure HausdorffUnitSphereMass EuclideanBallVolume
  MeasureRestriction MeasurePushforward MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_radius_sphere_mass]: the sphere factor in the
    radial coefficient calculation of Federer 3.2.36, p. 273, follows
    from the actual sphere dilation and unit-sphere normalization of
    3.2.13, p. 250. Every positive ambient dimension is retained;
    in dimension one the sphere has two positive H^0 atoms. *)
Theorem positive_radius_sphere_mass (R:realType) m (s:R):
  (0<m)%N ->0<s ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
    [set x|inner_norm (@euclidean_inner_productP R m) x=s]=
    (m%:R*euclidean_unit_ball_volume R m*s^+(m-1))%R%:E.
Proof.
move=>hm hs.
have h:=congr1 (fun mu=>mu setT) (@spherical_hausdorff_dilation_pushforward R m (m-1) s hs).
rewrite /spherical_hausdorff_measure /measure_scale /measure_pushforward
  /measure_restrict preimage_setT !setIT in h.
rewrite (@hausdorff_unit_sphere_mass R m hm) -EFinM mulrC in h.
exact h.
Qed.
