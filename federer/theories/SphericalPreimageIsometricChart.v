(** Federer (1969), 3.2.48, p. 285: the actual source tangent
    coordinates in the commutative diagram. The original manifold gives
    both planes and the unit word; the normalized horizontal lift proves
    an isometric bijection onto the actual preimage tangent. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductRestriction
  InnerNorm EuclideanHomInnerCharts OrthogonalMaps ProductInner ExteriorGrading
  ExteriorNorm SimpleElementary AssociatedSubspace EuclideanLinearMaps
  EuclideanGramDifferentialAlgebra EuclideanSubmanifoldUP UnitSphereSpace TangentConeUP
  EuclideanRectangularAdjoint SphericalProductPreimageImage SphericalCoordinateIsotropy SphericalTangentCoordinates
  SphericalHorizontalLift SphericalTranslatedTangentPlane GrassmannSimpleUnitRepresentative
  SphericalPreimageJacobian SphericalTranslatedTangentEquations SphericalTranslatedCartesianChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_isometric_chart]: the two exact
    source tangent rows of 3.2.48, p. 285. Every plane, word and inverse
    chart is proved to exist from the original class-one manifold.
    No globally chosen frame, degree restriction or Jacobian is a premise. *)
Theorem spherical_preimage_isometric_chart (R:realType) d r
    (c:R_n R (1+d)) (E:set (R_n R (1+d)))
    (g Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K:subspace (Hom (R_n R (1+d)) (R_n R (1+d)))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  @is_euclidean_submanifold R (1+d)%N r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R (1+d) ->
  spherical_orthogonal_preimage c E g ->
  (forall w,K w <->euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0 /\w c=0) ->
  exists (sigma:exterior_power (R_n R d) r)
    (T:G (Hom (R_n R (1+d)) (R_n R (1+d))) (r+d*(d-1)%/2)%N),
    simple sigma /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 /\
    (forall u,FedererSimple.T sigma u <->norm_tangent_cone
      (inner_norm (@euclidean_inner_productP R (1+d))) E (g c)
      (g (spherical_transverse_embedding Q u))) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c E) g=(grassmann_val T:set _) /\
    let P:lmodType R:=[the lmodType R of (subspace_space K*subspace_space (FedererSimple.T sigma))%type] in
    exists (i:Hom P (subspace_space (grassmann_val T))) (j:Hom (subspace_space (grassmann_val T)) P),
      cancel i j /\cancel j i /\
      is_orthogonal_map
        (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
          (restricted_inner_productP (@euclidean_inner_productP R d) (FedererSimple.T sigma)))
        (@restricted_inner_product R _ (@euclidean_hom_inner_product R (1+d) (1+d)) (grassmann_val T))
        (hom_as_linear i) /\
      forall x,subspace_val (i x)=hom_comp g (subspace_val x.1+
        (Num.sqrt (2:R))^-1*:spherical_horizontal_lift (hom_of_linear (linear_id (R_n R (1+d)))) c
          (spherical_transverse_embedding Q (subspace_val x.2))).
Proof.
move=>hc hQ hQc hMan hSphere hg hK.
have [S [hRange hS]]:=@spherical_translated_tangent_plane R d r c E g Q hQ hQc hMan hSphere hg.
have [sigma [hsigma [hUnit hSigma]]]:=@grassmann_simple_unit_representative R
  (euclidean_two_nonzero R) (R_n R d) (@euclidean_inner_product R d) (@euclidean_inner_productP R d) r S.
have [T [hT hJac]]:=@spherical_preimage_tangent_jacobian R d r c E g hc hMan hSphere hg.
have hPlane u:FedererSimple.T sigma u <->norm_tangent_cone
    (inner_norm (@euclidean_inner_productP R (1+d))) E (g c)
    (g (spherical_transverse_embedding Q u)).
  exact (iff_trans (hSigma u) (hS u)).
have hEquations w:grassmann_val T w <->
    euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d))))
      (hom_comp (euclidean_rectangular_adjoint g) w)=0 /\
    FedererSimple.T sigma (spherical_transverse_coordinates Q
      ((hom_comp (euclidean_rectangular_adjoint g) w) c)).
  rewrite -hT.
  exact (@spherical_preimage_translated_tangent_equations R d r c E g Q
    (FedererSimple.T sigma) hc hQ hQc hMan hSphere hg hPlane w).
exists sigma,T; split; first exact hsigma.
split; first exact hUnit.
split; first exact hPlane.
split; first exact hT.
exact (@spherical_translated_cartesian_chart R d c g Q K (FedererSimple.T sigma)
  (grassmann_val T) hc hg.1 hQ hQc hK hEquations).
Qed.
