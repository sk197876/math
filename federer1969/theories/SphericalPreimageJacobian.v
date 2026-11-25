(** Federer (1969), 3.2.47, p. 283: the actual
    r-th tangent Jacobian of Phi restricted to Phi inverse(E)
    equals 2^(-r/2). The original class-one E and
    original ambient Hilbert Hom metric remain. All tangent
    and horizontal quotient obligations are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates HomCompositionDeterminant LinearBasis EuclideanInnerProduct InnerProductUP
  InnerProductRestriction InnerNorm OrthogonalMaps EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanLinearMaps EuclideanSubmanifoldUP SubmanifoldTangentPlane
  FiniteInnerTangentPlane TangentConeUP UnitSphereSpace UnitSphereSubsetTangents
  SphericalHorizontalLift SphericalOrthogonalTangents SphericalOrthogonalOrbitDifferential
  SphericalOrthogonalPreimageSubmanifold SphericalOrthogonalPreimageTangent
  SphericalHorizontalQuotientJacobian SphericalProductPreimageImage
  InnerExteriorPositivity ExteriorMaps OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_plane_jacobian]: the exact
    Jr Phi on the actual preimage tangent, last display
    of 3.2.47, p. 283. The tangent plane's
    geometric equality is explicit; target tangent existence,
    every lift containment and the exterior norm are proved. *)
Theorem spherical_preimage_plane_jacobian (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (g:Hom (R_n R n.+1) (R_n R n.+1))
    (T:G (Hom (R_n R n.+1) (R_n R n.+1)) (r+n*(n-1)%/2)%N):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage c E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    (spherical_orthogonal_preimage c E) g=(grassmann_val T:set _) ->
  let hT:=restricted_inner_productP (@euclidean_hom_inner_productP R n.+1 n.+1) (grassmann_val T) in
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hT r)
    (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_inner_productP R n.+1) r)
    (exterior_power_map (hom_as_linear (hom_comp (spherical_orthogonal_orbit c)
      (hom_of_linear (subspace_inclusion (grassmann_val T))))) r) (((Num.sqrt (2:R))^-1)^+r).
Proof.
move=>hc hMan hSphere hg hTan hT.
have hUnit:euclidean_inner_product c c= 1.
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R n.+1)) hc expr1n.
have [U hU]:=@submanifold_tangent_plane R n.+1 r 1%N E (g c) (leqnn 1) hMan hg.2.
have hPreimage:=@spherical_orthogonal_preimage_tangent R n r c E g hc hMan hSphere hg.
have hPerp v (hv:grassmann_val U v):euclidean_inner_product (g c) v=0.
  apply:(@unit_sphere_subset_tangent_orthogonal R (R_n R n.+1)
    (@euclidean_inner_product R n.+1) (@euclidean_inner_productP R n.+1) E (g c)
    hSphere (hSphere (g c) hg.2) v).
  by rewrite hU.
apply:(@spherical_horizontal_quotient_exterior_norm R n.+1 r g c (grassmann_val T) U
  hg.1 hUnit hPerp).
- move=>w hw.
  have hW:norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage c E) g w by rewrite hTan.
  rewrite hPreimage in hW.
  by rewrite (spherical_orthogonal_tangent_gram hg.1) in hW; exact hW.1.
- move=>w hw.
  have hW:norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage c E) g w by rewrite hTan.
  rewrite hPreimage in hW; rewrite -hU; exact hW.2.
- move=>v hv.
  rewrite -hTan hPreimage; split.
  + rewrite (spherical_orthogonal_tangent_gram hg.1).
    exact (@spherical_horizontal_lift_tangent R n.+1 g c v hg.1).
  + rewrite (@spherical_horizontal_lift_evaluation R n.+1 g c v hUnit (@hPerp v hv)) hU.
    exact hv.
Qed.

(** Source for [spherical_preimage_tangent_jacobian]: existence
    of the actual preimage tangent plane and its computed
    r-Jacobian, 3.2.47, p. 283. No tangent,
    rank, derivative field or Jacobian is an extra premise. *)
Theorem spherical_preimage_tangent_jacobian (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (g:Hom (R_n R n.+1) (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage c E g ->
  exists T:G (Hom (R_n R n.+1) (R_n R n.+1)) (r+n*(n-1)%/2)%N,
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage c E) g=(grassmann_val T:set _) /\
    let hT:=restricted_inner_productP (@euclidean_hom_inner_productP R n.+1 n.+1) (grassmann_val T) in
    is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hT r)
      (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_inner_productP R n.+1) r)
      (exterior_power_map (hom_as_linear (hom_comp (spherical_orthogonal_orbit c)
        (hom_of_linear (subspace_inclusion (grassmann_val T))))) r) (((Num.sqrt (2:R))^-1)^+r).
Proof.
move=>hc hMan hSphere hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
have hPreMan:=@spherical_orthogonal_preimage_submanifold R n r 1%N c E hc (leqnn 1) hMan hSphere.
have [T hT]:=@finite_inner_submanifold_tangent_plane R H _
  (@euclidean_hom_inner_productP R n.+1 n.+1) _
  (@hom_rank_one_base R V V n.+1 n.+1 (@coordinate_basis R n.+1)
    (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1))
  (@hom_rank_one_baseP R V V n.+1 n.+1 (@coordinate_basis R n.+1)
    (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1))
  (r+n*(n-1)%/2)%N 1%N (spherical_orthogonal_preimage c E) g (leqnn 1) hPreMan hg.
exists T; split; first exact hT.
exact (@spherical_preimage_plane_jacobian R n r c E g T hc hMan hSphere hg hT).
Qed.
