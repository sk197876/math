(** Federer (1969), 1.7.9, p. 35: the product of linear maps is the sum of
    the products of their images of an orthonormal basis. The auxiliary
    finite basis used to obtain the dual metric does not affect the product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerDual InnerPolarity InnerPolaritySurjection
  TensorInner TensorInnerContraction TensorUP TensorProduct AlgebraTensor
  Hom Gamma GammaIntrinsic LinearBasis HomInner OrthonormalFamilies
  OneFormLinear OneFormIdentification FiniteDualDimension AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hom_inner_basis_independent]: Federer 1.7.9,
    p. 35, supporting intrinsicness: the product is independent of
    the finite basis supplied to construct the canonical isomorphism
    and the dual inner product. *)
Theorem hom_inner_basis_independent (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e)
    k (b : 'I_k -> V) (hb : is_basis b) (f g : Hom V W) :
  hom_inner hB hC he f g = hom_inner hB hC hb f g.
Proof.
rewrite !hom_innerE.
rewrite (@Gamma_basis_independent R V W (Finite.clone 'I_n _) (Finite.clone 'I_k _) e b he hb f).
rewrite (@Gamma_basis_independent R V W (Finite.clone 'I_n _) (Finite.clone 'I_k _) e b he hb g).
refine (@tensor_bilinear_ext R (A_m V R^o 1) W (A_m V R^o 1) W R^o
  (tensor_inner (inner_dual_productP hB he) hC)
  (tensor_inner (inner_dual_productP hB hb) hC)
  (inner_bilinear (tensor_inner_productP (inner_dual_productP hB he) hC))
  (inner_bilinear (tensor_inner_productP (inner_dual_productP hB hb) hC)) _ _ _).
move=> a w a' w'; rewrite !tensor_innerE.
by rewrite (inner_dual_product_basis_independent hB he hb).
Qed.

(** Source for [hom_inner_orthonormal_sum]: Federer 1.7.9,
    p. 35, first displayed computation: the product of maps is the
    sum of the products of their values on an orthonormal basis.
    The target space may have arbitrary dimension. *)
Theorem hom_inner_orthonormal_sum (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    k (e : 'I_k -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (f g : Hom V W) :
  hom_inner hB hC hb f g = \sum_i C (f (e i)) (g (e i)).
Proof.
rewrite (hom_inner_basis_independent hB hC hb he) hom_innerE !GammaE.
apply: tensor_inner_orthonormal_contraction.
move=> i j.
have hp l : one_form (dual_basis he l) = inner_polarity hB (e l).
  apply: one_hom_injective; rewrite one_formK.
  exact: esym (@inner_polarity_orthonormal_dual R V B hB k e he ho l).
by rewrite !hp inner_dual_polarityE ho.
Qed.
