(** Federer (1969), 3.2.35, p. 271:
    intrinsic volumes of the original nonempty
    bounded convex set are actual finite
    projected-volume averages. No measurability
    of the original source is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CoveringFamilyUP MetricBoundedUnion MetricBoundedClosureLaws ConvexProjectedClosureVolume
  IntegralGeometricFirstGaugeIntegral IntegralGeometricGauge ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBeta BoundedProjectedVolumeNorm NonnegativeExtendedExponentNorm
  NonnegativeExtendedExponentNormUP TopologicalBorel BorelClosedProjection SuslinSetUP
  PartialFunctionBasic MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_intrinsic_volume_integral]:
    the defining actual average for zeta^m(S)
    in Federer 3.2.35, p. 271, under
    precisely the original convex-source hypotheses.
    Compact closure makes projected averages
    measurable, while proved pointwise volume
    agreement restores every original coefficient.
    All natural dimensions, including zero, remain. *)
Theorem convex_intrinsic_volume_integral (R:realType) n m (hmn:(m<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projected_volume_function (m:=m) S))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_gauge R n m hmn 1 S).
Proof.
move=>hNonempty hS hBound.
have hSuslin:is_suslin_set R (closure S):=metric_borel_suslin (closed_borel_set (@closed_closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S)).
have hi:=@integral_geometric_first_gauge_integral R n m hmn (closure S) hSuslin.
have hFunction:projected_volume_function (m:=m) (closure S)=projected_volume_function (m:=m) S.
  apply:funext=>p; exact:convex_projected_closure_volume hNonempty hS hBound.
by rewrite hFunction (@convex_integral_geometric_gauge_closure R n m hmn 1 S hNonempty hS hBound) in hi.
Qed.

(** Source for [convex_intrinsic_volume_nonnegative_finite]:
    finiteness of the actual coefficients in
    Steiner's formula, Federer 3.2.35, p. 271.
    The existing bounded projected-volume norm
    theorem applies to the source closure, and
    the proved exact closure identity restores S.
    A finite scalar part is used only after
    its finiteness has been proved. This support
    permits every exponent at least one. *)
Theorem convex_intrinsic_volume_nonnegative_finite (R:realType) n m (hmn:(m<=n)%N) t
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->1<=t ->
  0<=@integral_geometric_gauge R n m hmn t S /\
    @integral_geometric_gauge R n m hmn t S< +oo.
Proof.
move=>hNonempty hS hBound ht.
rewrite -(@convex_integral_geometric_gauge_closure R n m hmn t S hNonempty hS hBound).
have hSuslin:is_suslin_set R (closure S):=metric_borel_suslin (closed_borel_set (@closed_closure [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] S)).
split; first exact:(@integral_geometric_gauge_nonnegative R n m hmn t ht (closure S) hSuslin).
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hClosureBound:=metric_bounded_closure hBound.
have [c [_ hRadius]]:=@metric_bounded_distance_bound R [the metricType R of X]
  (closure S) (0%R:X) hClosureBound.
have hNormBound x:closure S x ->(inner_norm (@euclidean_inner_productP R n) x<=c)%R.
  move=>hx; have hh:=hRadius x hx.
  by rewrite inner_metric_distanceE sub0r inner_normN in hh.
pose N:=nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
  (projected_volume_function (m:=m) (closure S)) t.
have hFinite:N< +oo:=@bounded_projected_volume_norm_finite R n m hmn (closure S) c t hNormBound hSuslin ht.
have hNonnegative:0<=N:=@nonnegative_extended_exponent_norm_ge0 R _ _ _ t
  (@theta_star_is_measure R n m hmn) (fun p=>projected_volume_function_nonnegative (closure S) p) ht
  (@theta_star_projected_volume_measurable R n m hmn (closure S) hSuslin).
have hFiniteNumber:N \is a fin_num by rewrite (ge0_fin_numE hNonnegative).
have hValue:N=(fine N)%:E by rewrite fineK.
change ((@projection_beta R n m hmn t)^-1%R%:E*N< +oo).
by rewrite hValue -EFinM; exact:ltry.
Qed.
