(** Federer (1969), 3.2.17, pp. 254–255:
    density bounds, exact tangent plane and
    relative composite differentiation for a
    biLipschitz parametrization at a full-density
    source point with injective differential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP HilbertFormCompactness NormDifferentialUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasureRestriction MeasureSetDensity CenteredBallRelations
  EuclideanLebesgueDimensions HausdorffMeasure MetricDensities MetricBiLipschitzUP
  TangentConeUP RelativeDifferentialUP MeasureApproximateTangentUP
  EuclideanBiLipschitzLowerDensity EuclideanBiLipschitzUpperDensity
  EuclideanBiLipschitzTangentPlanes EuclideanBiLipschitzRelativeComposite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_17]: the complete
    lemma in Federer 3.2.17, pp. 254–255.
    The factors lambda^(-2m) and lambda^(2m)
    bound the lower and upper metric densities;
    both tangent cones equal the differential
    image, and the relative differential composed
    with Dpsi equals the composite differential. *)
Theorem federer_3_2_17 (R : realType) m n
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) (lambda : R) a
    (L : Hom (R_n R m) (R_n R n)) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  1<lambda -> K a -> injective L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a L ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  let nu := measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K) in
  (((lambda^+(m+m))^-1)%R%:E<=lower_metric_density m nu (psi a))%E /\
  (lower_metric_density m nu (psi a)<=upper_metric_density m nu (psi a))%E /\
  (upper_metric_density m nu (psi a)<=(lambda^+(m+m))%R%:E)%E /\
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
    nu m (psi a)=norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (psi @` K) (psi a) /\
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (psi @` K) (psi a)=range L /\
  forall k (F : R_n R n -> R_n R k) (H : Hom (R_n R m) (R_n R k)),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H ->
    exists d : partial_function (R_n R n) (R_n R k),
      @has_relative_norm_differential R (R_n R n) (R_n R k)
        (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R k))
        (inner_norm_real_norm (@euclidean_inner_productP R n)) setT (psi @` K) F (psi a) d /\
      partial_function_precompose L d=partial_function_total H.
Proof.
move=> hB hLam ha hi hPsi hFull nu.
have hLam0 : 0<lambda := lt_trans (@ltr01 R) hLam.
have hTan := euclidean_bilipschitz_tangent_planes hB hLam0 ha hi hPsi hFull.
split; first exact: euclidean_bilipschitz_lower_density hB hLam0 ha hFull.
split; first exact: metric_densities_ordered.
split; first exact: euclidean_bilipschitz_upper_density hB hLam0 ha.
split; first exact hTan.1.
split; first exact hTan.2.
move=> k F H hComp.
exact: (@euclidean_bilipschitz_relative_composite R m n (R_n R k)
  (inner_norm (@euclidean_inner_productP R k))
  (inner_norm_real_norm (@euclidean_inner_productP R k))
  K psi F lambda a L H hB hLam0 ha hi hPsi hComp hFull).
Qed.
