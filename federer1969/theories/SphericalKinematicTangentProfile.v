(** Federer (1969), 3.2.48, pp. 285–286: the actual intrinsic
    tangent Jacobian profile in fixed isometric ambient coordinates.
    The existing sealed partial exterior norm supplies the profile;
    tangent words are chosen only inside pointwise existence proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates CoordinateProjection LinearBasis HomCompositionDeterminant
  EuclideanInnerProduct InnerProductUP InnerNorm EuclideanHomInnerCharts HilbertFormCompactness
  ProductInner OrthogonalMaps FiniteInnerChartUP EuclideanSubmanifoldUP UnitSphereSpace
  ExteriorGrading ExteriorNorm ExteriorHomogeneousProducts AssociatedSubspace SimpleElementary HodgeMaps
  EuclideanLinearMaps EuclideanRectangularAdjoint NormDifferentialUP NormDifferentialDirectional
  SphericalCoordinateIsotropy SphericalTangentCoordinates SphericalProductPreimageImage
  SphericalOrthogonalPreimageSubmanifold SphericalKinematicManifoldJacobian
  FiniteInnerCartesianSubmanifoldTangents FiniteInnerCartesianTangentJacobian
  OrthogonalKinematicMap OrthogonalKinematicDifferential OrthogonalKinematicCoordinateDifferential
  EuclideanTangentExteriorNorm TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_tangent_profile]: the actual
    J_nu Psi on the original manifold product in 3.2.48, p. 286,
    expressed by the existing sealed tangent exterior norm. No selected
    unit-word field, tangent frame or derivative witness enters this value. *)
Definition spherical_kinematic_tangent_profile (R:realType) d n v
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))):=
  @euclidean_tangent_exterior_norm R n v ((d*(d-1)%/2)+d)%N
    (p @` [set w:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
      spherical_orthogonal_preimage c A w.1 /\spherical_orthogonal_preimage c B w.2])
    (p z) (orthogonal_kinematic_coordinate_differential e t (p z)).

(** Source for [spherical_kinematic_tangent_profile_value]: the
    original intrinsic Jacobian equals sqrt(2)^(mu+lambda) times the
    starred tangent-word wedge norm, 3.2.48, p. 286. This is an exact
    pointwise equality on the original manifold product at any fixed
    transverse frame, with every derivative and tangent obligation proved. *)
Theorem spherical_kinematic_tangent_profile_value (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (x y Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (E:exterior_power (R_n R d) d) n v
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v)):
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
  exists (sigma:exterior_power (R_n R d) k) (tau:exterior_power (R_n R d) m),
    simple sigma /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 /\
    simple tau /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau= 1 /\
    (forall u,FedererSimple.T sigma u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
      A (x c) (x (spherical_transverse_embedding Q u))) /\
    (forall u,FedererSimple.T tau u <->norm_tangent_cone (inner_norm (@euclidean_inner_productP R (1+d)))
      B (y c) (y (spherical_transverse_embedding Q u))) /\
    spherical_kinematic_tangent_profile c A B e p t (x,y)=
      (Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d)
        (exterior_product (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)
          (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau)).
Proof.
move=>hc hQ hQc hA hB hAS hBS hx hy hE hChart ht.
pose H:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
have [sigma [tau [TX [TY [D [hsigma [hSigma [htau [hTau [hS [hT [hTX [hTY [hD hNorm]]]]]]]]]]]]]]:=
  @spherical_kinematic_manifold_jacobian_at_frame R d k m hk hm hkm c A B x y Q E
    hc hQ hQc hA hB hAS hBS hx hy hE.
have hSame:D=orthogonal_kinematic_differential x y.
  exact (@norm_differential_unique R [the lmodType R of (H*H)%type] H _ _
    (inner_norm_real_norm (product_inner_productP hH hH)) (inner_norm_real_norm hH)
    setT (@orthogonal_kinematic_map R (1+d)) (x,y) D (orthogonal_kinematic_differential x y)
    hD (orthogonal_kinematic_differential_actual x y)).
rewrite hSame in hNorm.
have hPX:=@spherical_orthogonal_preimage_submanifold R d k 1%N c A hc (leqnn 1) hA hAS.
have hPY:=@spherical_orthogonal_preimage_submanifold R d m 1%N c B hc (leqnn 1) hB hBS.
have hTan:=@finite_inner_cartesian_submanifold_tangent R H H _ _ hH hH
  (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N (spherical_orthogonal_preimage c A)
  (spherical_orthogonal_preimage c B) x y hPX hPY hx hy.
rewrite hTX hTY in hTan.
pose b:=@hom_rank_one_base R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)).
have hb:=@hom_rank_one_baseP R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)).
have hPartial:=@finite_inner_cartesian_tangent_partial_jacobian R H H H _ _ _ hH hH hH
  _ _ b b hb hb n v e p t
  [set z:H*H|spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2]
  (x,y) (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N TX TY (orthogonal_kinematic_differential x y)
  ((d*(d-1)%/2)+d)%N _ hChart ht hTan hNorm.
exists sigma,tau; split; first exact hsigma.
split; first exact hSigma.
split; first exact htau.
split; first exact hTau.
split; first exact hS.
split; first exact hT.
rewrite /spherical_kinematic_tangent_profile /orthogonal_kinematic_coordinate_differential
  (finite_inner_chart_right_inverse hChart).
exact (euclidean_tangent_exterior_norm_value hPartial).
Qed.
