(** Federer (1969), 1.7.11, p. 36: the operator norm of the top exterior
    power of the difference map on the two associated spaces. Both Hodge
    maps use any one unit ambient volume. The formula is independent of that
    orientation. The proof reuses the product-space identity of 1.6.5 and
    the metric results of 1.7.6 and 1.7.8; see SubspaceDifferenceNormBasis.v
    for the precise proof departure. Source context and the local erratum
    check: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerExteriorPositivity ExteriorNorm
  ExteriorMaps ExteriorGrading ExteriorHomogeneousProducts LinearBasis
  GramSchmidt OrthonormalisationUP AssociatedSubspace SimpleElementary
  SubspaceCarrier ProductInner SubspaceDifference SubspaceDifferenceNormBasis HodgeMaps HodgeProductOrientation
  OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [subspace_difference_norm]: Federer 1.7.11,
    p. 36, main identity in full: for simple unit k- and
    l-vectors with k+l>=n, the norm of exterior_n(x,y maps to x-y)
    on T(x) times T(y) is sqrt(2)^(k+l-n) times |star(x) wedge star(y)|.
    Its norm is specified by the proved unit-ball bound and attainment.
    The explicit k,l<=n proofs only type the Hodge maps; they follow
    from the unit hypotheses by unit_exterior_degree_bound. No
    transversality, positive-degree, or positive-dimension restriction
    is added, and no bases of the associated spaces are assumed. *)
Theorem subspace_difference_norm (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    k l (hk : (k <= n)%N) (hl : (l <= n)%N) (hkl : (n <= k+l)%N)
    (x : exterior_power V k) (y : exterior_power V l)
    (sx : simple x) (sy : simple y)
    (hx : exterior_norm h2 hB x = 1) (hy : exterior_norm h2 hB y = 1) :
  is_operator_norm
    (exterior_inner_productP h2 (subspace_product_innerP hB (FedererSimple.T x) (FedererSimple.T y)) n)
    (exterior_inner_productP h2 hB n)
    (exterior_power_map (GRing.Linear.clone _ _ _ _
      (subspace_difference (FedererSimple.T x) (FedererSimple.T y)) _) n)
    ((Num.sqrt (2 : R))^+(k+l-n) * exterior_norm h2 hB
      (exterior_product (hodge_vector h2 hB E hk x) (hodge_vector h2 hB E hl y))).
Proof.
have [e [he hoe]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal hoe.
rewrite (@hodge_product_basis_volume R h2 V B hB n e he ho E hE k l hk hl x y).
exact (@subspace_difference_norm_basis_volume R h2 V B hB n e he ho
  k l hk hl hkl x y sx sy hx hy).
Qed.
