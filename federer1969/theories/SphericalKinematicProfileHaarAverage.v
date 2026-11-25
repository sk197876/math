(** Federer (1969), 3.2.48, pp. 285–286: the actual intrinsic
    tangent Jacobian profile in fixed isometric ambient coordinates.
    The existing sealed partial exterior norm supplies the profile;
    tangent words are chosen only inside pointwise existence proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
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
  EuclideanTangentExteriorNorm TangentConeUP SphericalKinematicTangentProfile
  SphericalKinematicProfileIsotropy SphericalIsotropyTransverseAction HodgeWedgeHaarAverage
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology CompactGroupHaarNormalisation
  InnerMetric TopologicalGroupUP HomSpaceTopology HaarIntegralUP GammaHalfSequences MeasureUP MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_profile_haar_average]: the
    actual isotropy average of J_nu Psi in 3.2.48, p. 286. The original
    tangent norm, actual right stabilizer action and normalized Haar
    measure are used. Its finite integral is proved from 2.7.16(6),
    without an independent orbit-integrability or orientation premise. *)
Theorem spherical_kinematic_profile_haar_average (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (x y Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (E:exterior_power (R_n R d) d) n v
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (mulS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (invS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (eS:euclidean_orthogonal_group R d) (theta:set (euclidean_orthogonal_group R d)->\bar R):
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
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (euclidean_orthogonal_group R d) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  is_measure_integral theta (real_total_integrand (fun g:euclidean_orthogonal_group R d=>
    spherical_kinematic_tangent_profile c A B e p t
      (x,hom_comp y (euclidean_rectangular_adjoint
        (spherical_isotropy_transverse_operator Q (orthogonal_element_map g))))))
    (((Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d)))*
      (gamma_half_sequence R k*gamma_half_sequence R m/
        (gamma_half_sequence R d*gamma_half_sequence R (k+m-d))))%:E.
Proof.
move=>hc hQ hQc hA hB hAS hBS hx hy hE hChart ht hGroup hTheta.
have [sigma [tau [hsigma [hSigma [htau [hTau [hS [hT hValue]]]]]]]]:=
  @spherical_kinematic_tangent_profile_value R d k m hk hm hkm c A B x y Q E n v e p t
    hc hQ hQc hA hB hAS hBS hx hy hE hChart ht.
pose C:=(Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d)).
pose W:=fun g:euclidean_orthogonal_group R d=>exterior_norm (euclidean_two_nonzero R)
  (@euclidean_inner_productP R d) (exterior_product
    (exterior_power_map (hom_as_linear (orthogonal_element_map g)) (d-m)
      (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau))
    (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)).
have hMean:=@hodge_wedge_haar_average R (euclidean_two_nonzero R) d k m hk hm hkm
  E sigma tau mulS invS eS theta hGroup hTheta hE hsigma hSigma htau hTau.
have [[lam [hInvariant hMeasure hRepresentation hRegular]] hTotal]:=hTheta.
have hScale:=@real_total_integral_scale R _ theta hMeasure W
  (gamma_half_sequence R k*gamma_half_sequence R m/
    (gamma_half_sequence R d*gamma_half_sequence R (k+m-d))) C hMean.
have hFunction:(fun g:euclidean_orthogonal_group R d=>
    spherical_kinematic_tangent_profile c A B e p t
      (x,hom_comp y (euclidean_rectangular_adjoint
        (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)))))=
    (fun g=>C*W g).
  apply:funext=>g.
  exact (@spherical_kinematic_profile_isotropy R d k m hk hm hkm c A B x y Q E n v e p t sigma tau
    (orthogonal_element_map g) hc hQ hQc hA hB hAS hBS hx hy hE hChart ht
    hsigma hSigma htau hTau hS hT (orthogonal_element_orthogonal g)).
rewrite hFunction; exact hScale.
Qed.
