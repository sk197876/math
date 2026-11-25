(** Federer (1969), 3.2.48, pp. 285–286: two
    applications of 1.7.11 compute subtraction on the
    two source tangent sums sharing the vertical space.
    This supporting calculation uses the actual Cartesian maps,
    includes singular horizontal differences and all zero degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  InnerProductUP InnerProductRestriction ProductInner ProductFiniteBasis LinearBasis
  OrthogonalMaps ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm ExteriorHomogeneousProducts ExteriorOperatorNorm
  InnerExteriorPositivity OperatorNormUP AssociatedSubspace SimpleElementary
  SimpleUnitAssociatedLift SubspaceDifference SubspaceDifferenceNorm HodgeMaps
  CartesianTopExteriorNorm CartesianDifferenceExteriorNorm CartesianFourFactorShuffle
  ExteriorIsometricPrecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [common_vertical_difference_hom]: supporting the
    two actual subtraction blocks in 3.2.48, p. 285.
    Regrouping the four source factors separates the common
    vertical difference from the horizontal subspace difference. *)
Definition common_vertical_difference_hom (R:realType) (K V:lmodType R)
    (S T:subspace V):=
  hom_comp (cartesian_linear_hom (@cartesian_difference_hom R K)
    (hom_of_linear (GRing.Linear.clone _ _ _ _ (subspace_difference S T) _)))
    (@cartesian_four_factor_shuffle_hom R K (subspace_space S) K (subspace_space T)).

(** Source for [common_vertical_difference_exterior_norm]: the
    product sqrt(2)^mu sqrt(2)^lambda times the norm
    of the two starred tangent words, 3.2.48,
    p. 286, derived by the two printed applications
    of 1.7.11. No transversality or positive wedge
    norm is assumed, and zero vertical/horizontal degrees remain. *)
Theorem common_vertical_difference_exterior_norm (R:realType) (h2:(1+1:R)!=0)
    (K V:lmodType R) BK BV (hK:@is_inner_product R K BK) (hV:@is_inner_product R V BV)
    mu d (a:'I_mu->K) (b:'I_d->V) (ha:is_basis a) (hb:is_basis b)
    (E:exterior_power V d) (hE:exterior_norm h2 hV E= 1)
    k m (hk:(k<=d)%N) (hm:(m<=d)%N) (hkm:(d<=k+m)%N)
    (x:exterior_power V k) (y:exterior_power V m)
    (hsX:simple x) (hsY:simple y) (hX:exterior_norm h2 hV x= 1) (hY:exterior_norm h2 hV y= 1):
  let S:=FedererSimple.T x in let T:=FedererSimple.T y in
  let hS:=restricted_inner_productP hV S in let hT:=restricted_inner_productP hV T in
  is_operator_norm
    (exterior_inner_productP h2
      (product_inner_productP (product_inner_productP hK hS) (product_inner_productP hK hT)) (mu+d))
    (exterior_inner_productP h2 (product_inner_productP hK hV) (mu+d))
    (exterior_power_map (hom_as_linear (@common_vertical_difference_hom R K V S T)) (mu+d))
    ((Num.sqrt (2:R))^+(mu+(k+m-d))*exterior_norm h2 hV
      (exterior_product (hodge_vector h2 hV E hk x) (hodge_vector h2 hV E hm y))).
Proof.
move=>S T hS hT.
pose U:lmodType R:=[the lmodType R of (subspace_space S*subspace_space T)%type].
pose KK:lmodType R:=[the lmodType R of (K*K)%type].
pose Q:lmodType R:=[the lmodType R of (KK*U)%type].
pose P:lmodType R:=[the lmodType R of ((K*subspace_space S)*(K*subspace_space T))%type].
pose Z:lmodType R:=[the lmodType R of (K*V)%type].
pose hU:=product_inner_productP hS hT.
pose hKK:=product_inner_productP hK hK.
pose hQ:=product_inner_productP hKK hU.
pose hP:=product_inner_productP (product_inner_productP hK hS) (product_inner_productP hK hT).
pose hZ:=product_inner_productP hK hV.
pose D:=@cartesian_difference_hom R K.
pose A:Hom U V:=hom_of_linear (GRing.Linear.clone _ _ _ _ (subspace_difference S T) _).
pose F:=cartesian_linear_hom D A.
pose W:=@cartesian_four_factor_shuffle_hom R K (subspace_space S) K (subspace_space T).
pose I:=@cartesian_four_factor_shuffle_hom R K K (subspace_space S) (subspace_space T).
pose c:=exterior_norm h2 hV (exterior_product (hodge_vector h2 hV E hk x) (hodge_vector h2 hV E hm y)).
have [e [he _]]:=@simple_unit_associated_lift R h2 V BV hV k x hsX hX.
have [f [hf _]]:=@simple_unit_associated_lift R h2 V BV hV m y hsY hY.
have hHorizontal:=@subspace_difference_norm R h2 V BV hV d b hb E hE k m hk hm hkm x y hsX hsY hX hY.
have hHorizontalValue:exterior_operator_norm h2 hU hV (cartesian_basisP he hf) (hom_as_linear A) d=
    (Num.sqrt (2:R))^+(k+m-d)*c.
  have hExterior u:exterior_power_map (hom_as_linear A) d u=
      exterior_power_map (GRing.Linear.clone _ _ _ _ (subspace_difference S T) _) d u.
    apply:exterior_power_map_ext=>z; by [].
  have hNorm:is_operator_norm (exterior_inner_productP h2 hU d)
      (exterior_inner_productP h2 hV d) (exterior_power_map (hom_as_linear A) d)
      ((Num.sqrt (2:R))^+(k+m-d)*c).
    constructor.
    - move=>u hu; change (exterior_norm h2 hV (exterior_power_map (hom_as_linear A) d u)<=
        (Num.sqrt (2:R))^+(k+m-d)*c).
      rewrite hExterior; exact (operator_norm_unit_bound hHorizontal hu).
    - have [u [hu hValue]]:=operator_norm_attained hHorizontal.
      exists u; split; first exact hu.
      change (exterior_norm h2 hV (exterior_power_map (hom_as_linear A) d u)=
        (Num.sqrt (2:R))^+(k+m-d)*c).
      by rewrite hExterior.
  exact (operator_norm_unique (exterior_operator_normP h2 hU hV (cartesian_basisP he hf) (hom_as_linear A) d)
    hNorm).
have hBlockValue:exterior_operator_norm h2 hQ hZ
    (cartesian_basisP (cartesian_basisP ha ha) (cartesian_basisP he hf)) (hom_as_linear F) (mu+d)=
    (Num.sqrt (2:R))^+(mu+(k+m-d))*c.
  rewrite (@cartesian_top_exterior_norm R h2 KK U K V _ _ BK BV hKK hU hK hV
    (mu+mu)%N (k+m)%N mu d (cartesian_basis a a) (cartesian_basis e f) a b
    (cartesian_basisP ha ha) (cartesian_basisP he hf) ha hb D A).
  rewrite (@cartesian_difference_top_exterior_norm R h2 K BK hK mu a ha) hHorizontalValue.
  by rewrite exprD mulrA.
have hBlock:=exterior_operator_normP h2 hQ hZ
  (cartesian_basisP (cartesian_basisP ha ha) (cartesian_basisP he hf)) (hom_as_linear F) (mu+d)%N.
rewrite hBlockValue in hBlock.
have hLeft:cancel (hom_as_linear I) (hom_as_linear W).
  exact (@cartesian_four_factor_shuffleK R K K (subspace_space S) (subspace_space T)).
have hRight:cancel (hom_as_linear W) (hom_as_linear I).
  exact (@cartesian_four_factor_shuffleK R K (subspace_space S) K (subspace_space T)).
have hIso:is_orthogonal_map (product_inner hKK hU)
    (product_inner (product_inner_productP hK hS) (product_inner_productP hK hT)) (hom_as_linear I).
  exact (cartesian_four_factor_shuffle_orthogonal hK hK hS hT).
apply:(@exterior_isometric_precomposition_norm R h2 Q P Z _ _ _ hQ hP hZ
  (hom_as_linear I) (hom_as_linear W) (hom_as_linear F)
  (hom_as_linear (@common_vertical_difference_hom R K V S T)) (mu+d)%N
  ((Num.sqrt (2:R))^+(mu+(k+m-d))*c) hLeft hRight hIso _ hBlock).
move=>z; change (F (W (I z))=F z); by rewrite hLeft.
Qed.
