(** Federer (1969), 3.2.36, p. 272:
    the actual finite scalar projection integral
    has the original normalized intrinsic volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectedVolumeMeasurability EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence PartialFunctionUP
  PartialFunctionBasic SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_intrinsic_scalar_integral]:
    supporting continuity of the functions zeta^m
    in Federer 3.2.36, p. 272.
    The actual probability integral of the
    scalar projected volumes equals beta_1(n,m)
    times the actual scalar intrinsic volume.
    Every finite-part use is justified by
    compact image finiteness or the already
    proved bounded-convex coefficient theorem.
    No total value is invented at infinity,
    and every natural degree m<=n remains. *)
Theorem compact_convex_intrinsic_scalar_integral (R:realType) n m (hmn:(m<=n)%N)
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))):
  is_inner_convex (val A) ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (real_total_integrand (fun p:orthogonal_projection_metric_space R n m=>
      fine (projected_volume_function (val A) p)))
    ((@projection_beta R n m hmn 1* fine (@integral_geometric_gauge R n m hmn 1 (val A)))%R%:E).
Proof.
move=>hA.
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
have hBound:=compact_metric_diameter_finite A.
have hIntegral:=@convex_intrinsic_volume_integral R n m hmn (val A) (set_valP A).2 hA hBound.
have [hNonnegative hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n m hmn 1 (val A)
  (set_valP A).2 hA hBound (lexx 1).
have hGaugeNum:@integral_geometric_gauge R n m hmn 1 (val A) \is a fin_num.
  by rewrite (ge0_fin_numE hNonnegative).
have hValue:((@projection_beta R n m hmn 1)%:E*@integral_geometric_gauge R n m hmn 1 (val A))%E=
    (@projection_beta R n m hmn 1* fine (@integral_geometric_gauge R n m hmn 1 (val A)))%R%:E.
  by rewrite [RHS]EFinM (fineK hGaugeNum).
rewrite hValue in hIntegral.
have hVolumeNum (p:P):projected_volume_function (val A) p \is a fin_num.
  rewrite (ge0_fin_numE (projected_volume_function_nonnegative (val A) p)).
  exact:(@euclidean_compact_finite R m (euclidean_projection_linear p @` val A)
    (@euclidean_projected_compact_image R n m p (val A) (set_valP A).1)).
have hGraph (p:P) (y:extended_real_line R):
    partial_function_graph (partial_function_total (projected_volume_function (m:=m) (val A))) p y <->
    partial_function_graph (real_total_integrand (fun q:P=>fine (projected_volume_function (val A) q))) p y.
  by rewrite real_total_integrand_graph (fineK (hVolumeNum p)).
exact:measure_integral_graph_equivalent hGraph hIntegral.
Qed.
