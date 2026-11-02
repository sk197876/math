(** Federer (1969), 1.7.11, p. 36: the unit top volume of S times T obtained
    from the two given unit volumes. Supporting consequence of the product
    orthonormal basis and the one-dimensional top exterior power in 1.3.4,
    p. 16. Source context: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ProductInner ProductLinearMaps
  ProductFiniteBasis ProductOrthonormalBasis LinearBasis GramSchmidt
  OrthonormalisationUP ExteriorNorm ExteriorMaps ExteriorGrading
  ExteriorHomogeneousProducts ExteriorDeterminant FiniteExteriorPowers
  CovectorProductNaturality ConcatenatedProducts Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [product_top_norm]: Federer 1.7.11, p. 36,
    supporting multiplicativity of the norms of top vectors in
    separate Cartesian factors. In particular two unit top vectors
    give a unit top vector of the product. Either dimension may be zero. *)
Theorem product_top_norm (R : rcfType) (h2 : (1+1 : R) != 0)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n m (b : 'I_n -> V) (c : 'I_m -> W)
    (hb : is_basis b) (hc : is_basis c)
    (x : exterior_power V n) (y : exterior_power W m) :
  exterior_norm h2 (product_inner_productP hB hC)
    (exterior_product
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@product_left R V W) _) n x)
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@product_right R V W) _) m y)) =
  exterior_norm h2 hB x * exterior_norm h2 hC y.
Proof.
have [e [he hoe]] := @orthonormal_basis_exists R V B hB n b hb.
have [f [hf hof]] := @orthonormal_basis_exists R W C hC m c hc.
have ho := orthonormalisation_orthonormal hoe.
have hp := orthonormalisation_orthonormal hof.
rewrite {1 2}(@top_expansion R h2 n V e he x)
  {1 2}(@top_expansion R h2 m W f hf y) !linearZ.
rewrite (bilZl (@exterior_product_bilinear R
    (GRing.Lmodule.clone R (V * W)%type _) n m))
  (bilZr (@exterior_product_bilinear R
    (GRing.Lmodule.clone R (V * W)%type _) n m))
  !exterior_norm_scale /top_vector /finite_e_lambda
  !exterior_basis_product_natural concatenated_product
  (orthonormal_product_unit_norm h2 hB ho)
  (orthonormal_product_unit_norm h2 hC hp).
have hprod := @cartesian_basis_orthonormal R V W B C hB hC n m e f ho hp.
rewrite (@orthonormal_product_unit_norm R h2
  (GRing.Lmodule.clone R (V * W)%type _) (product_inner hB hC)
  (product_inner_productP hB hC) (n+m) (ProductFiniteBasis.cartesian_basis e f) hprod).
by rewrite !mulr1.
Qed.
