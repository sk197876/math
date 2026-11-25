(** Federer (1969), 1.7.11, p. 36: the full difference-map formula, first
    with the orientation of an orthonormal ambient basis. The proof uses
    1.6.5 for the product-space algebra, 1.7.6 for the top-target operator
    norm, and 1.7.8 for the norm-preserving duality. This replaces the
    displayed adapted basis calculation by these already established book
    identities. the exact supporting references are recorded in the imported
    metric lemmas. Source context and erratum check: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerProductRestriction InnerPolarity
  InnerExterior InnerExteriorBasis InnerExteriorPositivity ExteriorNorm
  ExteriorCovectorInner ExteriorOperatorNorm OperatorNormUP ExteriorMaps
  ExteriorGrading ExteriorHomogeneousProducts AlternatingCoordinates
  CovectorProducts FiniteExteriorPowers LinearBasis OrthonormalFamilies
  AssociatedSubspace SimpleElementary SubspaceCarrier
  ProductInner ProductLinearMaps ProductFiniteBasis ProductTopNorm
  SubspaceDifference SubspaceProductInclusion SimpleUnitAssociatedLift
  EmbeddedTopContractionNorm ProductSpaceMaps ProductContraction
  ProductContractionNorm HodgeMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [subspace_difference_norm_basis_volume]: Federer
    1.7.11, p. 36, main displayed identity, with both Hodge
    maps formed using the top product of an orthonormal basis.
    The scalar sqrt(2)^(k+l-n) is the printed 2^(lambda/2).
    The conclusion specifies the actual operator norm by its unit-ball
    laws, without requiring a supplied basis of either associated space.
    It includes nontransverse subspaces and dimension zero. *)
Theorem subspace_difference_norm_basis_volume
    (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
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
      (exterior_product
        (hodge_vector h2 hB (e_lambda e (ord_tuple n)) hk x)
        (hodge_vector h2 hB (e_lambda e (ord_tuple n)) hl y))).
Proof.
pose S := FedererSimple.T x; pose T := FedererSimple.T y.
pose US := GRing.Lmodule.clone R (subspace_space S) _.
pose UT := GRing.Lmodule.clone R (subspace_space T) _.
pose U := GRing.Lmodule.clone R (US * UT)%type _.
pose W := GRing.Lmodule.clone R (V * V)%type _.
pose hS := restricted_inner_productP hB S.
pose hT := restricted_inner_productP hB T.
pose hU := subspace_product_innerP hB S T.
pose hW := product_inner_productP hB hB.
have [a [ha [hua hxa]]] := @simple_unit_associated_lift R h2 V B hB k x sx hx.
have [b [hb [hub hyb]]] := @simple_unit_associated_lift R h2 V B hB l y sy hy.
pose u : exterior_power US k := e_lambda a (ord_tuple k).
pose v : exterior_power UT l := e_lambda b (ord_tuple l).
pose p : {linear US -> U} := GRing.Linear.clone _ _ _ _ (@product_left R US UT) _.
pose q : {linear UT -> U} := GRing.Linear.clone _ _ _ _ (@product_right R US UT) _.
pose z := exterior_product (exterior_power_map p k u) (exterior_power_map q l v).
have hz : exterior_norm h2 hU z = 1.
  change (exterior_norm h2 (product_inner_productP hS hT) z = 1).
  rewrite (@product_top_norm R h2 US UT _ _ hS hT k l a b ha hb u v).
  by rewrite hua hub mulr1.
pose i : {linear U -> W} := GRing.Linear.clone _ _ _ _ (subspace_product_inclusion S T) _.
pose f : {linear U -> V} := GRing.Linear.clone _ _ _ _ (subspace_difference S T) _.
pose omega := omega_lambda h2 (fun j => inner_polarity hB (e j)) (Lambda_top n).
have homega : exterior_covector_norm h2 hB he omega = 1.
  rewrite /omega -inner_exterior_basis_covectors inner_exterior_form_norm.
  exact: orthonormal_product_unit_norm.
have hn := @embedded_top_contraction_norm R h2 U V W
  (subspace_product_inner hB S T) B (product_inner hB hB) hU hB hW
  (k+l) n (ProductFiniteBasis.cartesian_basis a b) e (ProductFiniteBasis.cartesian_basisP ha hb) he hkl
  i (@subspace_product_inclusion_orthogonal R V S T B hB) f (FedererProduct.f_map V)
  (@subspace_difference_factorisation R V S T) z hz omega homega.
have hi : exterior_power_map i (k+l) z =
    exterior_product (exterior_power_map (FedererProduct.P_map V) k x)
      (exterior_power_map (FedererProduct.Q_map V) l y).
  rewrite /z /i subspace_product_exterior_inclusion hxa hyb; by [].
rewrite hi in hn.
have hn2 := @product_contraction_norm R h2 V B hB n e he ho k l hk hl hkl x y.
rewrite /FedererProductContraction.product_contraction in hn2.
rewrite -hn2 -hn.
exact: exterior_operator_normP.
Qed.
