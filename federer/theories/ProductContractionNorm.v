(** Federer (1969), 1.7.11, p. 36: the metric identity obtained from the
    product-space identity 1.6.5, pp. 25-26. This proof uses that earlier
    identity instead of repeating its basis computation. The remaining
    identification with the operator norm uses the source product's unit
    volume. Source context and the absence of a corresponding. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity ProductInner
  ProductSpaceIdentity ProductContraction ProductSpaceMaps
  DiagonalExteriorNorm DualProductHodgeNorm ExteriorNorm ExteriorNormNaturality
  ExteriorGrading ExteriorHomogeneousProducts FiniteExteriorPowers
  AlternatingCoordinates CovectorProducts OrthonormalFamilies LinearBasis
  HodgeMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [product_contraction_norm]: Federer 1.7.11,
    p. 36, supporting norm computation for the contraction in
    1.6.5. Its value is sqrt(2)^(k+l-n) times the norm of
    the wedge of Hodge duals. This computation holds for arbitrary
    multivectors; simplicity is needed for the subsequent comparison
    with the operator norm on their associated spaces. *)
Theorem product_contraction_norm (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    k l (hk : (k <= n)%N) (hl : (l <= n)%N) (hkl : (n <= k+l)%N)
    (x : exterior_power V k) (y : exterior_power V l) :
  exterior_norm h2 (product_inner_productP hB hB)
    (FedererProductContraction.product_contraction h2 hkl
      (omega_lambda h2 (fun i => inner_polarity hB (e i)) (Lambda_top n)) x y) =
  (Num.sqrt (2 : R))^+(k+l-n) *
    exterior_norm h2 hB (exterior_product
      (hodge_vector h2 hB (e_lambda e (val (Lambda_top n))) hk x)
      (hodge_vector h2 hB (e_lambda e (val (Lambda_top n))) hl y)).
Proof.
have hd i j : inner_polarity hB (e i) [tuple e j] = if i==j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
rewrite (@product_space_contraction R h2 V n e
  (fun i => inner_polarity hB (e i)) he hd k l hk hl hkl x y)
  /FedererProductContraction.diagonal_dual_product
  exterior_norm_scale normrX normrN normr1 expr1n mul1r
  diagonal_exterior_norm exterior_norm_reindex.
congr (_ * _).
exact (@dual_product_hodge_norm R h2 V B hB n e he ho k l hk hl
  (product_contraction_bound hk hl hkl) x y).
Qed.
