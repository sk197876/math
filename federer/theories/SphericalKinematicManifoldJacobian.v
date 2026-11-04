(** Federer (1969), 3.2.48, pp. 285–286: the original source
    manifolds determine the actual tangent planes, local unit words and
    the computed tangent exterior norm of the original differential.
    Every chart and vertical-plane obligation is discharged. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier LinearBasis
  FiniteCoordinates CoordinateProjection GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerProductRestriction
  InnerNorm EuclideanHomInnerCharts OrthogonalMaps ProductInner ExteriorGrading ExteriorMaps
  ExteriorNorm ExteriorHomogeneousProducts InnerExteriorPositivity OperatorNormUP
  SimpleElementary AssociatedSubspace HodgeMaps EuclideanLinearMaps
  EuclideanGramDifferentialAlgebra EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  HomCompositionDeterminant NormDifferentialUP OrthogonalKinematicMap OrthogonalKinematicIsometries
  CartesianTopExteriorNorm CommonVerticalDifferenceExteriorNorm SphericalKinematicTargetEmbedding
  SphericalKinematicDifferentialDiagram SphericalCoordinateIsotropy
  ExteriorIsometricPrecomposition ExteriorIsometricPostcomposition
  GrassmannSubspaces SimpleProducts SphericalKinematicChartJacobian SphericalVerticalTangentPlane
  SphericalPreimageIsometricChart SphericalTangentCoordinates EuclideanSubmanifoldUP
  UnitSphereSpace TangentConeUP SphericalProductPreimageImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_manifold_jacobian_at_frame]:
    the same actual Jacobian calculation in 3.2.48, pp. 285–286,
    for any fixed local orthonormal transverse frame. This exact scope
    permits averaging all stabilizer actions in that one frame. *)
Theorem spherical_kinematic_manifold_jacobian_at_frame (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (x y Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (E:exterior_power (R_n R d) d):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  @is_euclidean_submanifold R (1+d)%N k 1%N A ->
  @is_euclidean_submanifold R (1+d)%N m 1%N B ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  spherical_orthogonal_preimage c A x ->spherical_orthogonal_preimage c B y ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1 ->
  exists (sigma:exterior_power (R_n R d) k) (tau:exterior_power (R_n R d) m)
    (TX:G (Hom (R_n R (1+d)) (R_n R (1+d))) (k+d*(d-1)%/2)%N)
    (TY:G (Hom (R_n R (1+d)) (R_n R (1+d))) (m+d*(d-1)%/2)%N)
    (D:Hom [the lmodType R of
        ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type]
        (Hom (R_n R (1+d)) (R_n R (1+d)))),
    simple sigma /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 /\
    simple tau /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau= 1 /\
    (forall u,FedererSimple.T sigma u <->norm_tangent_cone
      (inner_norm (@euclidean_inner_productP R (1+d))) A (x c) (x (spherical_transverse_embedding Q u))) /\
    (forall u,FedererSimple.T tau u <->norm_tangent_cone
      (inner_norm (@euclidean_inner_productP R (1+d))) B (y c) (y (spherical_transverse_embedding Q u))) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c A) x=(grassmann_val TX:set _) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c B) y=(grassmann_val TY:set _) /\
    has_norm_differential
      (inner_norm (product_inner_productP
        (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
      (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      setT (@orthogonal_kinematic_map R (1+d)) (x,y) D /\
      is_operator_norm
        (exterior_inner_productP (euclidean_two_nonzero R)
          (product_inner_productP
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) (grassmann_val TX))
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) (grassmann_val TY))) ((d*(d-1)%/2)+d))
        (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_hom_inner_productP R (1+d) (1+d)) ((d*(d-1)%/2)+d))
        (exterior_power_map (hom_as_linear (hom_comp D
          (cartesian_linear_hom (hom_of_linear (subspace_inclusion (grassmann_val TX)))
            (hom_of_linear (subspace_inclusion (grassmann_val TY)))))) ((d*(d-1)%/2)+d))
        ((Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d)
          (exterior_product (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)
            (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau))).
Proof.
move=>hc hQ hQc hA hB hASphere hBSphere hx hy hE.
have [K hKernel]:=spherical_vertical_tangent_plane hc.
have hK w:grassmann_val K w <->
    euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0 /\w c=0.
  by rewrite -hKernel.
have [sigma [TX [hsigma [hSigma [hS [hTX [i [j [hij [hji [hi hiValue]]]]]]]]]]]:=
  @spherical_preimage_isometric_chart R d k c A x Q (grassmann_val K)
    hc hQ hQc hA hASphere hx hK.
have [tau [TY [htau [hTau [hT [hTY [l [r [hlr [hrl [hl hlValue]]]]]]]]]]]:=
  @spherical_preimage_isometric_chart R d m c B y Q (grassmann_val K)
    hc hQ hQc hB hBSphere hy hK.
have [b hb]:=grassmann_proof K.
have hIValue a:subspace_val (i a)=hom_comp x
    (spherical_kinematic_target_embedding_hom c Q (grassmann_val K) (a.1,subspace_val a.2)).
  exact (hiValue a).
have hLValue a:subspace_val (l a)=hom_comp y
    (spherical_kinematic_target_embedding_hom c Q (grassmann_val K) (a.1,subspace_val a.2)).
  exact (hlValue a).
have [D [hD hNorm]]:=@spherical_kinematic_chart_jacobian R d (d*(d-1)%/2)%N k m
  hk hm hkm c Q x y (grassmann_val K) (grassmann_val TX) (grassmann_val TY) b hb E sigma tau
  hc hQ hQc hx.1 hy.1 (fun w hw=>(hK w).1 hw) hE hsigma hSigma htau hTau
  i j l r hij hji hlr hrl hi hl hIValue hLValue.
exists sigma,tau,TX,TY,D.
split; first exact hsigma.
split; first exact hSigma.
split; first exact htau.
split; first exact hTau.
split; first exact hS.
split; first exact hT.
split; first exact hTX.
split; first exact hTY.
split; first exact hD.
exact hNorm.
Qed.

(** Source for [spherical_kinematic_manifold_jacobian]: the actual
    tangent Jacobian calculation in 3.2.48, p. 286. The original
    class-one manifolds supply all planes and isometries; no supplied
    differential, chart or tangent norm is an extra hypothesis.
    The wedge may vanish and every zero-dimensional block remains. *)
Theorem spherical_kinematic_manifold_jacobian (R:realType) d k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (A B:set (R_n R (1+d)))
    (x y:Hom (R_n R (1+d)) (R_n R (1+d)))
    (E:exterior_power (R_n R d) d):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  @is_euclidean_submanifold R (1+d)%N k 1%N A ->
  @is_euclidean_submanifold R (1+d)%N m 1%N B ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  spherical_orthogonal_preimage c A x ->spherical_orthogonal_preimage c B y ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1 ->
  exists (Q:Hom (R_n R (1+d)) (R_n R (1+d)))
    (sigma:exterior_power (R_n R d) k) (tau:exterior_power (R_n R d) m)
    (TX:G (Hom (R_n R (1+d)) (R_n R (1+d))) (k+d*(d-1)%/2)%N)
    (TY:G (Hom (R_n R (1+d)) (R_n R (1+d))) (m+d*(d-1)%/2)%N)
    (D:Hom [the lmodType R of
        ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type]
        (Hom (R_n R (1+d)) (R_n R (1+d)))),
    is_orthogonal_map (@euclidean_inner_product R (1+d))
      (@euclidean_inner_product R (1+d)) (hom_as_linear Q) /\
    Q (spherical_coordinate_pole R d)=c /\
    simple sigma /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 /\
    simple tau /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau= 1 /\
    (forall u,FedererSimple.T sigma u <->norm_tangent_cone
      (inner_norm (@euclidean_inner_productP R (1+d))) A (x c) (x (spherical_transverse_embedding Q u))) /\
    (forall u,FedererSimple.T tau u <->norm_tangent_cone
      (inner_norm (@euclidean_inner_productP R (1+d))) B (y c) (y (spherical_transverse_embedding Q u))) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c A) x=(grassmann_val TX:set _) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      (spherical_orthogonal_preimage c B) y=(grassmann_val TY:set _) /\
    has_norm_differential
      (inner_norm (product_inner_productP
        (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
      (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
      setT (@orthogonal_kinematic_map R (1+d)) (x,y) D /\
      is_operator_norm
        (exterior_inner_productP (euclidean_two_nonzero R)
          (product_inner_productP
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) (grassmann_val TX))
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) (grassmann_val TY))) ((d*(d-1)%/2)+d))
        (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_hom_inner_productP R (1+d) (1+d)) ((d*(d-1)%/2)+d))
        (exterior_power_map (hom_as_linear (hom_comp D
          (cartesian_linear_hom (hom_of_linear (subspace_inclusion (grassmann_val TX)))
            (hom_of_linear (subspace_inclusion (grassmann_val TY)))))) ((d*(d-1)%/2)+d))
        ((Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d))*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d)
          (exterior_product (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)
            (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau))).
Proof.
move=>hc hA hB hASphere hBSphere hx hy hE.
have [Q [hQ hQc]]:=spherical_transverse_frame_exists hc.
have [sigma [tau [TX [TY [D h]]]]]:=@spherical_kinematic_manifold_jacobian_at_frame R d k m
  hk hm hkm c A B x y Q E hc hQ hQc hA hB hASphere hBSphere hx hy hE.
exists Q,sigma,tau,TX,TY,D; by split; last split.
Qed.
