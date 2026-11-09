(** Federer (1969), 3.3.20, p. 307: actual scalar coordinates of every original line projection. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  OrthonormalFamilies CoordinateProjection InnerNorm InnerMetric EuclideanOneCoordinate
  EuclideanProjectionSpace OrthogonalInjectionSpaces EuclideanRectangularAdjoint
  StructureProjectionDistance EuclideanRealPlane PlanePairNormGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_plane_inner_product_two_coordinates]: the
    actual dot product in the displayed P_u of 3.3.20, p. 307,
    in the two original scalar coordinates. *)
Lemma euclidean_plane_inner_product_two_coordinates (R:realType)
    (x y:inner_metric_space (@euclidean_inner_productP R 2)):
  euclidean_inner_product x y=
    euclidean_real_plane_first x * euclidean_real_plane_first y+
    euclidean_real_plane_second x * euclidean_real_plane_second y.
Proof.
rewrite !real_plane_first_coordinateE !real_plane_second_coordinateE
  /euclidean_inner_product big_ord_recl big_ord1 /=.
have hIndex:(lift ord0 ord0:'I_2)=ord_max by apply:val_inj.
by rewrite hIndex.
Qed.

(** Source for [planar_original_projection_unit_coordinates]: every
    original P in O*(2,1) has local unit coefficients u,v and its
    actual scalar value equals u*x_1+v*x_2, 3.3.20, p. 307. The
    original adjoint on the scalar unit proves this statement; no
    coordinate frame, selected normal or evaluation formula is assumed. *)
Theorem planar_original_projection_unit_coordinates (R:realType)
    (p:euclidean_projection_space R 2 1):
  exists u v:R,u^+2+v^+2= 1 /\
    forall x:inner_metric_space (@euclidean_inner_productP R 2),
      euclidean_one_project (euclidean_projection_linear p x)=
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x.
Proof.
pose e:=@coordinate_basis R 1 ord0.
pose w:=euclidean_rectangular_adjoint (orthogonal_projection_map p) e.
have hUnit:euclidean_inner_product w w= 1.
  rewrite /w structure_projection_adjoint_orthogonal euclidean_inner_basis.
  by rewrite /e /coordinate_basis ffunE eqxx.
exists (euclidean_real_plane_first w),(euclidean_real_plane_second w);split.
- by rewrite euclidean_plane_inner_product_two_coordinates -!expr2 in hUnit.
- move=>x.
  have hPair:euclidean_inner_product x w=(euclidean_projection_linear p x) ord0.
    by rewrite /w structure_projection_adjoint_pairing euclidean_inner_basis.
  rewrite /euclidean_one_project -hPair euclidean_plane_inner_product_two_coordinates.
  ring.
Qed.
