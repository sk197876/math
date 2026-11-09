(** Federer (1969), 3.3.20, p. 307: every actual unit direction gives an original O-star projection. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerMetric EuclideanRealPlane MetricCartesianProductUP PlanarProjectionCoordinates
  OrthonormalFamilies OrthogonalMaps OrthonormalFrameMap CoordinateProjection
  Adjoint AdjointUP EuclideanOneCoordinate EuclideanProjectionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [planar_unit_coordinate_projection_exists]: the
    original association u maps to P_u in O*(2,1), 3.3.20, p. 307.
    A one-vector orthonormal frame and its existing sealed adjoint
    prove existence and the exact scalar formula; the projection stays
    an existential witness and is used only through the exposed laws. *)
Theorem planar_unit_coordinate_projection_exists (R:realType) (u v:R):
  u^+2+v^+2= 1 ->exists p:euclidean_projection_space R 2 1,
    forall x:inner_metric_space (@euclidean_inner_productP R 2),
      euclidean_one_project (euclidean_projection_linear p x)=
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x.
Proof.
move=>hUnit.
pose w:=@euclidean_real_plane_pair R u v.
have hW:euclidean_inner_product w w= 1.
  rewrite euclidean_plane_inner_product_two_coordinates /w
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  by rewrite -!expr2.
pose e (_:'I_1):=w.
have hFrame:orthonormal_family (@euclidean_inner_product R 2) e.
  move=>i j;rewrite (ord1 i) (ord1 j) eqxx;exact:hW.
have [f [hf hfe]]:=@orthonormal_frame_map_exists R (R_n R 2)
  (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2) 1 e hFrame.
pose L:=inner_adjoint (@euclidean_inner_productP R 1) (@euclidean_inner_productP R 2)
  (@coordinate_basisP R 1) f.
have hAdj:is_adjoint (@euclidean_inner_product R 1) (@euclidean_inner_product R 2) f L
  :=inner_adjointP _ _ _ f.
have hL:O_star L by exists f;split.
have [p hp]:=euclidean_projection_linear_complete hL.
exists p=>x.
rewrite /euclidean_one_project hp.
have hPair:=hAdj (@coordinate_basis R 1 ord0) x.
rewrite hfe /e (inner_symmetric (@euclidean_inner_productP R 1)) euclidean_inner_basis in hPair.
rewrite hPair (inner_symmetric (@euclidean_inner_productP R 2))
  euclidean_plane_inner_product_two_coordinates /w
  (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
  (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
ring.
Qed.
