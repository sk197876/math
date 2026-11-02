(** Federer (1969), 3.2.35, p. 272:
    the actual distance-level masses are the
    lower-dimensional Steiner polynomial averages,
    with the exact Cauchy normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP EuclideanDistanceTubeBasic EuclideanDistanceTubeConvex ConvexDistanceLevelCauchy
  SteinerProjectedTubeAverage SteinerTubePolynomial ConvexIntrinsicVolumeIntegrals ProjectedVolumeMeasurability
  IntegralGeometricGauge ProjectionBeta EuclideanBallVolume HausdorffMeasure MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [steiner_distance_level_average]: the
    second and third equalities of Federer's
    dimension induction, 3.2.35, p. 272.
    The lower-dimensional Steiner induction supplies
    every actual projected tube volume. The
    proved average and the actual tube's gauge
    integral have a unique common value.
    Positivity cancels beta_1(n,n-1), and the
    whole original level Cauchy formula supplies
    its Hausdorff mass. This is an induction
    step, not an added final theorem premise. *)
Theorem steiner_distance_level_average (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d (t:R):
  (forall (A:set (inner_metric_space (@euclidean_inner_productP R k))) e,
    A!=set0 ->is_inner_convex A ->metric_set_bounded A ->is_metric_set_distance A e ->
    is_steiner_tube_volume A e) ->
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->(0<t)%R ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k [set x|d x=t]=
    (2/ @projection_beta R k.+1 k (leqnSn k) 1)%R%:E*
    (\sum_(i:'I_k.+1) (euclidean_unit_ball_volume R (k-i)*t^+(k-i))%R%:E*
      ((@projection_beta R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 /
        @projection_beta R k i (steiner_dimension_guard i) 1)%R%:E*
      @integral_geometric_gauge R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S)).
Proof.
move=>hIH hNonempty hS hBound hD ht.
pose T:set (inner_metric_space (@euclidean_inner_productP R k.+1)):=[set x|(d x<t)%R].
have hTNonempty:T!=set0:=@euclidean_distance_tube_nonempty R k.+1 S d t hNonempty hD ht.
have hTConvex:is_inner_convex T:=@euclidean_distance_tube_convex R k.+1 S d t hD hS.
have hTBound:metric_set_bounded T:=@euclidean_distance_tube_bounded R k.+1 S d t hNonempty hD hBound ht.
have hNormalized:=@convex_intrinsic_volume_integral R k.+1 k (leqnSn k) T hTNonempty hTConvex hTBound.
have hAverage:=@steiner_projected_tube_average R k S d t hIH hNonempty hS hBound hD ht.
have hMass:=(@convex_distance_level_cauchy R k S d t hNonempty hS hBound hD ht).2.
have hEquality:=measure_integral_unique hNormalized hAverage.
pose b:=@projection_beta R k.+1 k (leqnSn k) 1.
have hb:(0<b)%R:=@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx 1).
have hb0:(b!=0)%R by rewrite gt_eqF.
have hScaled:=congr1 (fun z : \bar R=>(2/b)%R%:E*z) hEquality.
have hCancel (z : \bar R):(2/b)%R%:E*(b%:E*z)= 2*z.
  by rewrite muleA -EFinM divfK.
rewrite hCancel in hScaled.
by rewrite -hMass in hScaled.
Qed.
