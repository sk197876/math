(** Federer (1969), 3.2.33, p. 270: the ordinary
    smooth differential is also the actual full-domain approximate
    differential on the open source cube. Supporting locality. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP EuclideanLebesgueDimensions
  HausdorffMeasure EuclideanHausdorffLebesgue MeasureUP MeasureRestriction PartialFunctionUP
  MetricDensities MetricDensityZero EuclideanMetricDensityConverse EuclideanFullDensityTangent
  MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_euclidean_approximate_tangent_full]:
    the original-domain interpretation of Df in the smooth
    example of Federer 3.2.33, p. 270, using 3.2.16,
    p. 252. At an interior point H^m restricted to W
    has the full Euclidean approximate tangent cone. Transfer
    each full-density test locally to Lebesgue measure, then
    apply the proved full-density tangent theorem. Neither
    global source measurability nor finite mass is needed. *)
Theorem open_euclidean_approximate_tangent_full (R:realType) m (W:set (R_n R m)) a:
  norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) W a ->
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R m))
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m) W) m a=setT.
Proof.
move=>[r [hr hBall]].
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose Leb:=@euclidean_lebesgue_measure R m.
have hHL:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m=Leb.
  apply:funext=>A; exact:(euclidean_hausdorff_spherical_lebesgue A).1.
apply/seteqP; split=>v; first by [].
move=>_ S hS.
rewrite hHL in hS.
have hRestrict:measure_restrict (measure_restrict Leb W) (~` S)=measure_restrict Leb (W `&` ~` S).
  apply:funext=>A; by rewrite /measure_restrict setIA.
rewrite hRestrict in hS.
have hLocal:exists d:R,0<d /\forall x,mdist (a:inner_metric_space (@euclidean_inner_productP R m)) x<d ->
    (~` S) x ->(W `&` ~` S) x.
  exists r; split; first exact hr.
  move=>x hx hNot; split; last exact hNot.
  have hSmall:N (x-a)<r.
    change (is_true (N (a-x)<r)) in hx.
    rewrite /N (real_seminorm_subtract hN.1); exact hx.
  have hW:=hBall (x-a) hSmall.
  by rewrite addrC subrK in hW.
have hFull:=@metric_restricted_density_zero_local_mono R
  (inner_metric_space (@euclidean_inner_productP R m)) m Leb (~` S) (W `&` ~` S) a
  (euclidean_lebesgue_is_measure R m) hLocal hS.
have hTan:=euclidean_full_density_tangent (euclidean_metric_zero_relative_zero_density hFull).
by rewrite hTan.
Qed.
