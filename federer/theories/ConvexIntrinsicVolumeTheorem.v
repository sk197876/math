(** Federer (1969), 3.2.36, pp. 272--273: the
    whole continuity, Cartesian product, box and isometric-invariance item. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  CompactHausdorffMetric EuclideanProjectionSpace EuclideanProjectionMetric
  CompactConvexVolumeContinuity CompactConvexProjectedVolumeJointContinuity CompactConvexIntrinsicVolumeContinuity
  EuclideanLebesgueDimensions ProjectedVolumeMeasurability IntegralGeometricGauge IntegralGeometricMeasure
  EuclideanCartesianMap SteinerTubePolynomial BoundedConvexCartesianIntrinsicVolumes
  EuclideanBoxUP ElementarySymmetricCoefficientsUP RectangularBoxIntrinsicVolumes
  BoundedConvexIsometricEmbedding ConvexIntegralGeometricIsometricEmbedding ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_36]: the complete numbered item in
    Federer 3.2.36, pp. 272--273. The actual Lebesgue volume,
    joint projected volume and normalized intrinsic volumes are
    continuous on the original compact convex Hausdorff domains.
    Arbitrary original nonempty bounded convex factors satisfy the
    full Cartesian convolution. Every rectangular box has the proved
    independently specified elementary symmetric edge coefficients,
    with actual finite extended intrinsic-volume values. Intrinsic
    volumes and Q_1 are invariant under arbitrary metric isometric
    injections. Source measurability, full dimension and positive mass
    are never added; all natural coordinate blocks and admissible
    degrees remain. Apply erratum p. 5, book p. 273 line 18:
    m-th in the box statement. The positive-reach references are
    historical discussion, not assumed additional theorems. *)
Theorem federer_3_2_36 (R:realType):
  (forall n,continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (euclidean_lebesgue_measure n (val A):extended_real_line R))) /\
  (forall n m,continuous (fun z:subspace (@compact_convex_projection_pairs R n m)=>
    (projected_volume_function (val z.2) z.1:extended_real_line R))) /\
  (forall n m (hmn:(m<=n)%N),continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (@integral_geometric_gauge R n m hmn 1 (val A):extended_real_line R))) /\
  (forall m n (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))),
    A!=set0 ->B!=set0 ->is_inner_convex A ->is_inner_convex B ->
    metric_set_bounded A ->metric_set_bounded B ->forall l:'I_(m+n).+1,
      @integral_geometric_gauge R (m+n) l (steiner_dimension_guard l) 1 (euclidean_cartesian_set A B)=
      (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N)
        @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A*
        @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B)%E) /\
  (forall n origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))),
    is_euclidean_rectangular_box origin axis c Q ->exists e:'I_n.+1->R,
      is_elementary_symmetric_coefficients c e /\forall j:'I_n.+1,
        @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=(e j)%:E) /\
  (forall m n k (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->inner_metric_space (@euclidean_inner_productP R n)),
    (forall x y,mdist (f x) (f y)=mdist x y) ->forall A:set (inner_metric_space (@euclidean_inner_productP R m)),
      A!=set0 ->is_inner_convex A ->metric_set_bounded A ->
      @integral_geometric_gauge R n k hkn 1 (f @` A)=@integral_geometric_gauge R m k hkm 1 A) /\
  (forall m n k (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->inner_metric_space (@euclidean_inner_productP R n)),
    (forall x y,mdist (f x) (f y)=mdist x y) ->forall A:set (inner_metric_space (@euclidean_inner_productP R m)),
      @convex_integral_geometric_measure R n k hkn 1 (f @` A)=
      @convex_integral_geometric_measure R m k hkm 1 A).
Proof.
repeat split.
- exact:compact_convex_volume_continuous.
- exact:compact_convex_projected_volume_joint_continuous.
- exact:compact_convex_intrinsic_volume_continuous.
- exact:bounded_convex_cartesian_intrinsic_volumes.
- exact:rectangular_box_elementary_symmetric_existence.
- move=>m n k hkm hkn f hMetric A hNonempty hConvex hBound.
  exact:bounded_convex_isometric_embedding_intrinsic_volume hNonempty hConvex hBound hMetric.
- exact:convex_integral_geometric_isometric_embedding.
Qed.
