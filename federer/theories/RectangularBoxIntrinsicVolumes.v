(** Federer (1969), 3.2.36, p. 273: the full
    rectangular-box assertion through its independent orthonormal carrier laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBoxUP EuclideanLinearMaps OrthogonalMaps OrthogonalFinite EuclideanRectangularBox
  AffineOrthogonalBijection BoundedConvexIsometricEmbedding CoordinateEdgeBoxGeometry
  CoordinateEdgeBoxIntrinsicPolynomial ElementarySymmetricCoefficientsUP IntegralGeometricGauge
  SteinerTubePolynomial ConvexIntrinsicFinitePart RectangularBoxCoordinateImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangular_box_elementary_symmetric_intrinsic_volumes]:
    the entire rectangular-box consequence in Federer 3.2.36,
    p. 273, with arbitrary original orthonormal axes and origin.
    Its actual intrinsic volumes satisfy the independent elementary
    symmetric coefficient laws of the side lengths. The actual frame
    isometry identifies the given box with the proved coordinate box;
    all carrier, metric and gauge obligations are discharged. Apply
    erratum p. 5, book p. 273 line 18: m-th. Zero edge
    lengths, lower-dimensional boxes and the empty R^0 edge family
    are retained, without an auxiliary box or volume hypothesis. *)
Theorem rectangular_box_elementary_symmetric_intrinsic_volumes (R:realType) n
    origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_rectangular_box origin axis c Q ->
  is_elementary_symmetric_coefficients c (fun j:'I_n.+1=>
    fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q)).
Proof.
move=>hQ.
have [F [hMetric hImage]]:=rectangular_box_isometric_coordinate_image hQ.
have hc:=euclidean_box_width_nonnegative_law hQ.
have hNonempty:=coordinate_edge_box_nonempty hc.
have hBound:=coordinate_edge_box_bounded hc.
have hCoeff (j:'I_n.+1):@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (coordinate_edge_box c).
  rewrite hImage; exact:(@bounded_convex_isometric_embedding_intrinsic_volume R n n j
    (steiner_dimension_guard j) (steiner_dimension_guard j) (coordinate_edge_box c) F
    hNonempty (@coordinate_edge_box_convex R n c) hBound hMetric).
move=>t; have h:=@coordinate_edge_box_elementary_symmetric_coefficients R n c hc t.
rewrite h; apply:eq_bigr=>j _; by rewrite hCoeff.
Qed.

(** Source for [rectangular_box_intrinsic_finite_value]: finite actual
    box coefficients in Federer 3.2.36, p. 273. The actual
    isometric coordinate identification transports the proved finite
    bounded-convex gauge value. Thus scalar coefficient use is justified
    before the unique elementary symmetric family is identified. *)
Lemma rectangular_box_intrinsic_finite_value (R:realType) n
    origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_rectangular_box origin axis c Q ->forall j:'I_n.+1,
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=
      (fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q))%:E.
Proof.
move=>hQ j.
have [F [hMetric hImage]]:=rectangular_box_isometric_coordinate_image hQ.
have hc:=euclidean_box_width_nonnegative_law hQ.
have hInvariant:@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (coordinate_edge_box c).
  rewrite hImage; exact:(@bounded_convex_isometric_embedding_intrinsic_volume R n n j
    (steiner_dimension_guard j) (steiner_dimension_guard j) (coordinate_edge_box c) F
    (coordinate_edge_box_nonempty hc) (@coordinate_edge_box_convex R n c)
    (coordinate_edge_box_bounded hc) hMetric).
rewrite hInvariant; exact:convex_intrinsic_finite_part_value (coordinate_edge_box_nonempty hc)
  (@coordinate_edge_box_convex R n c) (coordinate_edge_box_bounded hc).
Qed.

(** Source for [rectangular_box_intrinsic_volume_coefficient]: the full
    pointwise m-th elementary symmetric value in Federer 3.2.36,
    p. 273, with the erratum p. 5 correction at line 18.
    Every independently specified elementary symmetric family agrees
    with the actual extended intrinsic volumes, which are first proved
    finite. No extra finiteness premise or chosen coefficient family
    is imposed on the original rectangular box. *)
Corollary rectangular_box_intrinsic_volume_coefficient (R:realType) n
    origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))) (e:'I_n.+1->R):
  is_euclidean_rectangular_box origin axis c Q ->is_elementary_symmetric_coefficients c e ->
  forall j:'I_n.+1,@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=(e j)%:E.
Proof.
move=>hQ hE j; rewrite (rectangular_box_intrinsic_finite_value hQ j).
congr (_%:E); exact:elementary_symmetric_coefficients_unique
  (rectangular_box_elementary_symmetric_intrinsic_volumes hQ) hE j.
Qed.

(** Source for [rectangular_box_elementary_symmetric_existence]: proved
    existence of the independently specified coefficient family and
    all its actual intrinsic-volume values, Federer 3.2.36,
    p. 273. This is a local existential conclusion, retaining
    zero edges and ambient dimension zero without a new global choice. *)
Corollary rectangular_box_elementary_symmetric_existence (R:realType) n
    origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_rectangular_box origin axis c Q ->exists e:'I_n.+1->R,
    is_elementary_symmetric_coefficients c e /\forall j:'I_n.+1,
      @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q=(e j)%:E.
Proof.
move=>hQ; exists (fun j:'I_n.+1=>fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q)).
split; first exact:rectangular_box_elementary_symmetric_intrinsic_volumes hQ.
exact:rectangular_box_intrinsic_finite_value hQ.
Qed.
