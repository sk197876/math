(** Federer (1969), 3.2.48, pp. 285–286: the actual intrinsic
    tangent Jacobian profile in fixed isometric ambient coordinates.
    The existing sealed partial exterior norm supplies the profile;
    tangent words are chosen only inside pointwise existence proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates CoordinateProjection LinearBasis HomCompositionDeterminant
  EuclideanInnerProduct InnerProductUP InnerNorm EuclideanHomInnerCharts HilbertFormCompactness
  ProductInner OrthogonalMaps FiniteInnerChartUP EuclideanSubmanifoldUP UnitSphereSpace
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorHomogeneousProducts AssociatedSubspace SimpleElementary HodgeMaps
  EuclideanLinearMaps EuclideanRectangularAdjoint NormDifferentialUP NormDifferentialDirectional
  SphericalCoordinateIsotropy SphericalTangentCoordinates SphericalProductPreimageImage
  SphericalOrthogonalPreimageSubmanifold SphericalKinematicManifoldJacobian
  FiniteInnerCartesianSubmanifoldTangents FiniteInnerCartesianTangentJacobian
  OrthogonalKinematicMap OrthogonalKinematicDifferential OrthogonalKinematicCoordinateDifferential
  EuclideanTangentExteriorNorm TangentConeUP SphericalKinematicTangentProfile HodgeWedgeAssociatedPlanes
  SphericalKinematicTangentWordFormula SphericalIsotropyTransverseAction SphericalIsotropyTangentWords
  AssociatedSubspaceIsomorphism ExteriorNormNaturality HodgeOrthogonalTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_profile_isotropy]: the exact
    pointwise isotropy integrand before the Haar average in 3.2.48,
    p. 286. The actual original source, differential and sealed tangent
    norm are retained, and the transformed word is used only locally.
    The only removed sign has proved absolute value one. *)
Theorem spherical_kinematic_profile_isotropy (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (x y Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (E:exterior_power (R_n R d) d) n v
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (sigma:exterior_power (R_n R d) k) (tau:exterior_power (R_n R d) m)
    (h:Hom (R_n R d) (R_n R d)):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->Q (spherical_coordinate_pole R d)=c ->
  @is_euclidean_submanifold R (1+d)%N k 1%N A ->@is_euclidean_submanifold R (1+d)%N m 1%N B ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  spherical_orthogonal_preimage c A x ->spherical_orthogonal_preimage c B y ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1 ->
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R (1+d) (1+d))
    (@euclidean_hom_inner_productP R (1+d) (1+d))) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R (1+d) (1+d))
    (@euclidean_inner_product R v) (hom_as_linear t) ->
    simple sigma ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 ->
    simple tau ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau= 1 ->
    (forall u,FedererSimple.T sigma u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
      A (x c) (x (spherical_transverse_embedding Q u))) ->
    (forall u,FedererSimple.T tau u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
      B (y c) (y (spherical_transverse_embedding Q u))) ->
  is_orthogonal_map (@euclidean_inner_product R d) (@euclidean_inner_product R d) (hom_as_linear h) ->
  spherical_kinematic_tangent_profile c A B e p t
    (x,hom_comp y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)))=
    (Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d)
      (exterior_product
        (exterior_power_map (hom_as_linear h) (d-m)
          (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau))
        (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)).
Proof.
move=>hc hQ hQc hA hB hAS hBS hx hy hE hChart ht hsigma hSigma htau hTau hS hT hh.
pose y':=hom_comp y (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q h)).
pose tau':=exterior_power_map (hom_as_linear h) m tau.
have [hy' hPole]:=@spherical_isotropy_right_inverse_preimage R d c Q y h B hQ hQc hh hy.
have hsTau':simple tau':=exterior_power_map_simple (hom_as_linear h) htau.
have hTau':exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau'= 1.
  rewrite /tau' (@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R)
    (R_n R d) (R_n R d) _ _ (@euclidean_inner_productP R d) (@euclidean_inner_productP R d)
    (hom_as_linear h) hh m tau); exact hTau.
have hT':forall u,FedererSimple.T tau' u <->norm_tangent_cone
    (inner_norm (@euclidean_inner_productP R (1+d))) B (y' c) (y' (spherical_transverse_embedding Q u)).
  exact (@spherical_isotropy_translated_tangent_word R d m c Q y h B tau hQ hQc hh hy hT).
have hValue:=@spherical_kinematic_tangent_word_formula R d k m hk hm hkm c A B x y' Q E n v e p t
  sigma tau' hc hQ hQc hA hB hAS hBS hx hy' hE hChart ht hsigma hSigma hsTau' hTau' hS hT'.
rewrite hValue /tau'.
rewrite (@hodge_wedge_orthogonal_transport R (euclidean_two_nonzero R) (R_n R d)
  _ (@euclidean_inner_productP R d) d (@coordinate_basis R d) (@coordinate_basisP R d) E hE
  (hom_as_linear h) m hm tau (d-k)%N
  (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma) hh).
by rewrite exterior_product_norm_swap.
Qed.
