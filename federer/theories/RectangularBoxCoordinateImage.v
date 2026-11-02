(** Federer (1969), 3.2.36, p. 273: the full
    rectangular-box assertion through its independent orthonormal carrier laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBoxUP EuclideanLinearMaps OrthogonalMaps OrthogonalFinite EuclideanRectangularBox
  AffineOrthogonalBijection BoundedConvexIsometricEmbedding CoordinateEdgeBoxGeometry
  IntegralGeometricGauge SteinerTubePolynomial ConvexIntrinsicFinitePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangular_box_isometric_coordinate_image]: the actual
    orthonormal-coordinate identification of the box used in Federer
    3.2.36, p. 273, with the independent box laws of 2.7.16,
    p. 136. The internal frame map, proved orthogonal bijectivity
    and actual coordinate identities identify the original carrier
    with the translated isometric image of its coordinate box.
    Zero edge widths and the R^0 box are retained. *)
Lemma rectangular_box_isometric_coordinate_image (R:realType) n
    origin (axis:'I_n->R_n R n) (c:'I_n->R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_rectangular_box origin axis c Q ->
  exists F:inner_metric_space (@euclidean_inner_productP R n)->inner_metric_space (@euclidean_inner_productP R n),
    (forall x y,mdist (F x) (F y)=mdist x y) /\Q=F @` coordinate_edge_box c.
Proof.
move=>hQ.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose g:=euclidean_frame_map axis.
have hG:is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) g.
  exact:euclidean_frame_orthogonal (euclidean_box_orthonormal_law hQ).
pose F:X->X:=fun z=>origin+g z.
have [_ [_ [_ hMetric]]]:=affine_orthogonal_bijection_inverse origin hG.
have hSurj:=@orthogonal_endomorphism_surjective R (R_n R n) _ (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) g hG.
have hImage:Q=F @` coordinate_edge_box c.
  apply/seteqP; split=>x.
  - move=>hx; have [z hz]:=hSurj (x-origin); exists z.
    + move=>i; have h:0<=euclidean_inner_product (x-origin) (axis i)<=c i.
        exact:(euclidean_box_carrier_law hQ x).1 hx i.
      by rewrite -hz /g (euclidean_frame_inner (euclidean_box_orthonormal_law hQ)) in h.
    + rewrite /F hz addrC subrK; reflexivity.
  - move=>[z hz <-]; apply:(euclidean_box_carrier_law hQ (F z)).2=>i.
    rewrite /F [origin+g z]addrC addrK /g
      (euclidean_frame_inner (euclidean_box_orthonormal_law hQ)); exact:hz.
exists F; split; [exact hMetric|exact hImage].
Qed.
