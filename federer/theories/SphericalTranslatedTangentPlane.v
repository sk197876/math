(** Federer (1969), 3.2.48, p. 285: the
    actual translated tangent S(x)=x inverse Tan(A,Phi(x))
    in orthonormal transverse coordinates. Its dimension and
    exact range are proved from the original manifold;
    no tangent frame or degree bound is an extra premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates CoordinateProjection EuclideanInnerProduct
  InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  EuclideanSubmanifoldUP SubmanifoldTangentPlane TangentConeUP UnitSphereSpace
  UnitSphereSubsetTangents SphericalProductPreimageImage SphericalCoordinateIsotropy
  SphericalTangentCoordinates GrassmannInjectiveImageOn.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_translated_tangent_plane]: the actual
    k-plane S(x) in 3.2.48, p. 285, represented
    in the existing local isometric coordinates of the
    tangent hyperplane. The exact original tangent and inverse
    orthogonal action are retained, including dimension zero. *)
Theorem spherical_translated_tangent_plane (R:realType) d r
    (c:R_n R (1+d)) (E:set (R_n R (1+d)))
    (g Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  @is_euclidean_submanifold R (1+d)%N r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R (1+d) ->spherical_orthogonal_preimage c E g ->
  exists S:G (R_n R d) r,
    (grassmann_val S:set (R_n R d))=
      (fun v=>spherical_transverse_coordinates Q (euclidean_rectangular_adjoint g v)) @`
        norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d))) E (g c) /\
    forall u,grassmann_val S u <->
      norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d))) E (g c)
        (g (spherical_transverse_embedding Q u)).
Proof.
move=>hQ hQc hMan hSphere hg.
have [U hU]:=@submanifold_tangent_plane R (1+d)%N r 1%N E (g c) (leqnn 1) hMan hg.2.
pose M:=hom_comp (spherical_transverse_coordinates Q) (euclidean_rectangular_adjoint g).
have hPerp v (hv:grassmann_val U v):euclidean_inner_product c (euclidean_rectangular_adjoint g v)=0.
  rewrite euclidean_rectangular_adjoint_pairing.
  apply:(@unit_sphere_subset_tangent_orthogonal R (R_n R (1+d))
    (@euclidean_inner_product R (1+d)) (@euclidean_inner_productP R (1+d))
    E (g c) hSphere (hSphere _ hg.2) v).
  by rewrite hU.
have hRestore v (hv:grassmann_val U v):spherical_transverse_embedding Q (M v)=euclidean_rectangular_adjoint g v.
  apply:(@spherical_transverse_coordinates_inverse R d Q hQ).
  by rewrite hQc (hPerp v hv).
have hInjectiveOn v w (hv:grassmann_val U v) (hw:grassmann_val U w):M v=M w ->v=w.
  move=>hSame.
  have h:=congr1 (fun u=>g (spherical_transverse_embedding Q u)) hSame.
  by rewrite (hRestore v hv) (hRestore w hw) !(euclidean_orthogonal_adjoint_cancel_reverse hg.1) in h.
have [S hS]:=@grassmann_injective_image_on R (R_n R (1+d)) (R_n R d) r U M
  d (@coordinate_basis R d) (@coordinate_basisP R d) hInjectiveOn.
exists S; split.
- rewrite hS -hU; reflexivity.
- move=>u; split.
  + move=>hu; rewrite hS in hu; have [v hv hMv]:=hu.
    rewrite -hMv (hRestore v hv) (euclidean_orthogonal_adjoint_cancel_reverse hg.1) hU.
    exact hv.
  + move=>hTan; rewrite hS.
    exists (g (spherical_transverse_embedding Q u)); first by rewrite -hU.
    change (spherical_transverse_coordinates Q
      (euclidean_rectangular_adjoint g (g (spherical_transverse_embedding Q u)))=u).
    by rewrite (euclidean_orthogonal_adjoint_cancel hg.1) (spherical_transverse_coordinatesK hQ).
Qed.
