(** Federer (1969), 3.2.48, pp. 285–286: the actual differential
    on the two source tangent carriers has the computed exterior norm.
    The preceding geometric existence results discharge the chart laws;
    the two applications of 1.7.11 are transported by actual isometries. *)
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
  ExteriorIsometricPrecomposition ExteriorIsometricPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_chart_jacobian]: J_nu Psi equals
    sqrt(2)^(mu+lambda) times the norm of the wedge of the two starred
    actual tangent words, 3.2.48, p. 286. This supporting transport lemma
    takes the independently proved chart laws, retains singular pairs,
    and supplies the actual full ambient differential. *)
Theorem spherical_kinematic_chart_jacobian (R:realType) d mu k m
    (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (c:R_n R (1+d)) (Q x y:Hom (R_n R (1+d)) (R_n R (1+d)))
    (K TX TY:subspace (Hom (R_n R (1+d)) (R_n R (1+d))))
    (b:'I_mu->subspace_space K) (hb:is_basis b)
    (E:exterior_power (R_n R d) d)
    (sigma:exterior_power (R_n R d) k) (tau:exterior_power (R_n R d) m):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  Q (spherical_coordinate_pole R d)=c ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear x) ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear y) ->
  (forall w,K w ->euclidean_gram_differential (hom_of_linear (linear_id (R_n R (1+d)))) w=0 /\w c=0) ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E= 1 ->
  simple sigma ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) sigma= 1 ->
  simple tau ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d) tau= 1 ->
  let S:=FedererSimple.T sigma in let T:=FedererSimple.T tau in
  let PS:lmodType R:=[the lmodType R of (subspace_space K*subspace_space S)%type] in
  let PT:lmodType R:=[the lmodType R of (subspace_space K*subspace_space T)%type] in
  forall (i:Hom PS (subspace_space TX)) (j:Hom (subspace_space TX) PS)
    (l:Hom PT (subspace_space TY)) (r:Hom (subspace_space TY) PT),
    cancel i j ->cancel j i ->cancel l r ->cancel r l ->
    is_orthogonal_map
      (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
        (restricted_inner_productP (@euclidean_inner_productP R d) S))
      (@restricted_inner_product R _ (@euclidean_hom_inner_product R (1+d) (1+d)) TX) (hom_as_linear i) ->
    is_orthogonal_map
      (product_inner (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) K)
        (restricted_inner_productP (@euclidean_inner_productP R d) T))
      (@restricted_inner_product R _ (@euclidean_hom_inner_product R (1+d) (1+d)) TY) (hom_as_linear l) ->
    (forall a,subspace_val (i a)=hom_comp x
      (spherical_kinematic_target_embedding_hom c Q K (a.1,subspace_val a.2))) ->
    (forall a,subspace_val (l a)=hom_comp y
      (spherical_kinematic_target_embedding_hom c Q K (a.1,subspace_val a.2))) ->
    exists D:Hom [the lmodType R of
        ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type]
        (Hom (R_n R (1+d)) (R_n R (1+d))),
      has_norm_differential
        (inner_norm (product_inner_productP
          (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))))
        (inner_norm (@euclidean_hom_inner_productP R (1+d) (1+d)))
        setT (@orthogonal_kinematic_map R (1+d)) (x,y) D /\
      is_operator_norm
        (exterior_inner_productP (euclidean_two_nonzero R)
          (product_inner_productP
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) TX)
            (restricted_inner_productP (@euclidean_hom_inner_productP R (1+d) (1+d)) TY)) (mu+d))
        (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_hom_inner_productP R (1+d) (1+d)) (mu+d))
        (exterior_power_map (hom_as_linear (hom_comp D
          (cartesian_linear_hom (hom_of_linear (subspace_inclusion TX))
            (hom_of_linear (subspace_inclusion TY))))) (mu+d))
        ((Num.sqrt (2:R))^+(mu+(k+m-d))*exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R d)
          (exterior_product (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hk sigma)
            (hodge_vector (euclidean_two_nonzero R) (@euclidean_inner_productP R d) E hm tau))).
Proof.
move=>hc hQ hQc hx hy hK hE hsigma hSigma htau hTau S T PS PT i j l r hij hji hlr hrl hi hl hiValue hlValue.
pose H:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose hKInner:=restricted_inner_productP hH K.
pose hV:=@euclidean_inner_productP R d.
pose hS:=restricted_inner_productP hV S.
pose hT:=restricted_inner_productP hV T.
pose hTX:=restricted_inner_productP hH TX.
pose hTY:=restricted_inner_productP hH TY.
pose P:lmodType R:=[the lmodType R of (PS*PT)%type].
pose U:lmodType R:=[the lmodType R of (subspace_space TX*subspace_space TY)%type].
pose Z:lmodType R:=[the lmodType R of (subspace_space K*R_n R d)%type].
pose hP:=product_inner_productP (product_inner_productP hKInner hS) (product_inner_productP hKInner hT).
pose hU:=product_inner_productP hTX hTY.
pose hZ:=product_inner_productP hKInner hV.
pose I:=cartesian_linear_hom i l.
pose J:=cartesian_linear_hom j r.
pose A:=@common_vertical_difference_hom R (subspace_space K) (R_n R d) S T.
pose L:=spherical_kinematic_target_embedding_hom c Q K.
pose M:Hom H H:=hom_comp
  (hom_of_linear (@hom_left_composition R (R_n R (1+d)) (R_n R (1+d)) x))
  (hom_of_linear (@hom_right_composition R (R_n R (1+d)) (R_n R (1+d)) (euclidean_rectangular_adjoint y))).
pose V:=hom_comp M L.
pose C:=(Num.sqrt (2:R))^+(mu+(k+m-d))*exterior_norm (euclidean_two_nonzero R) hV
  (exterior_product (hodge_vector (euclidean_two_nonzero R) hV E hk sigma)
    (hodge_vector (euclidean_two_nonzero R) hV E hm tau)).
have hL:=@spherical_kinematic_target_embedding_orthogonal R d c Q K hc hQ hQc hK.
have hVOrth:is_orthogonal_map (product_inner hKInner hV)
    (@euclidean_hom_inner_product R (1+d) (1+d)) (hom_as_linear V).
  move=>a a'.
  change (euclidean_hom_inner_product (hom_comp x (hom_comp (L a) (euclidean_rectangular_adjoint y)))
    (hom_comp x (hom_comp (L a') (euclidean_rectangular_adjoint y)))=product_inner hKInner hV a a').
  rewrite (orthogonal_kinematic_sandwich_pairing _ _ (euclidean_orthogonal_adjoint_orthogonal hy) hx).
  exact (hL a a').
have hA:=@common_vertical_difference_exterior_norm R (euclidean_two_nonzero R)
  (subspace_space K) (R_n R d) _ _ hKInner hV mu d b (@coordinate_basis R d) hb
  (@coordinate_basisP R d) E hE k m hk hm hkm sigma tau hsigma htau hSigma hTau.
have hVA:is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hP (mu+d))
    (exterior_inner_productP (euclidean_two_nonzero R) hH (mu+d))
    (exterior_power_map (hom_as_linear (hom_comp V A)) (mu+d)) C.
  apply:(@exterior_isometric_postcomposition_norm R (euclidean_two_nonzero R)
    P Z H _ _ _ hP hZ hH (hom_as_linear A) (hom_as_linear V) (hom_as_linear (hom_comp V A))
    (mu+d)%N C hVOrth _ hA).
  by move=>a.
have [D [hD hDiagram]]:=@spherical_kinematic_differential_diagram R d c Q x y K S T hx hy
  (fun w hw=>(hK w hw).1).
exists D; split; first exact hD.
pose F:=hom_comp D (cartesian_linear_hom (hom_of_linear (subspace_inclusion TX))
  (hom_of_linear (subspace_inclusion TY))).
have hILeft:cancel (hom_as_linear I) (hom_as_linear J).
  move=>[a b']; change (J (I (a,b'))=(a,b')).
  by rewrite /I /J !cartesian_linear_homE hij hlr.
have hIRight:cancel (hom_as_linear J) (hom_as_linear I).
  move=>[a b']; change (I (J (a,b'))=(a,b')).
  by rewrite /I /J !cartesian_linear_homE hji hrl.
have hIOrth:is_orthogonal_map
    (product_inner (product_inner_productP hKInner hS) (product_inner_productP hKInner hT))
    (product_inner hTX hTY) (hom_as_linear I).
  move=>[a b'] [a' b''].
  change (product_inner hTX hTY (I (a,b')) (I (a',b''))=
    product_inner (product_inner_productP hKInner hS) (product_inner_productP hKInner hT)
      (a,b') (a',b'')).
  by rewrite /I !cartesian_linear_homE !product_innerE hi hl !product_innerE.
have hFValue z:F z=D (subspace_val z.1,subspace_val z.2).
  case:z=>u v.
  rewrite /F hom_compE cartesian_linear_homE.
  reflexivity.
have hIValue a b':I (a,b')=(i a,l b').
  exact (cartesian_linear_homE i l a b').
have hCommute z:F (I z)=hom_comp V A z.
  case:z=>a b'.
  rewrite hIValue hFValue hiValue hlValue.
  exact (hDiagram a b').
exact (@exterior_isometric_precomposition_norm R (euclidean_two_nonzero R)
  P U H _ _ _ hP hU hH (hom_as_linear I) (hom_as_linear J)
  (hom_as_linear (hom_comp V A)) (hom_as_linear F) (mu+d)%N C hILeft hIRight hIOrth hCommute hVA).
Qed.
