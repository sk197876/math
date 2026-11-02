(** Federer (1969), 1.7.5, p. 32: the Gram-Schmidt product calculation. The
    unit directions are used here; their diagonal coefficients give the
    lengths of the unnormalised residuals in the book. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorTriangular
  ExteriorNorm InnerNorm OrthonormalFamilies OrthonormalisationUP
  GramSchmidtTriangular AssociatedSubspace FullDegreeFactor SimpleProducts IndependentProducts
  FiniteIndependence FiniteSpans FiniteSpanSpace ModuleQuotient
  ExteriorGrading FiniteExteriorPowers Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Factor.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Variables u v : 'I_m -> V.
Hypothesis hu : finite_independent u.
Hypothesis hv : is_orthonormalisation B u v.

(** Source for [gram_schmidt_exterior_factor]: Federer
    1.7.5, p. 32, the original exterior product is the product
    of diagonal coefficients times the orthonormal exterior product.
    This is the normalised version of the displayed residual identity. *)
Theorem gram_schmidt_exterior_factor :
  e_lambda u (ord_tuple m) =
    (foldr ( *%R) 1 [seq B (u i) (v i) | i <- enum 'I_m]) *:
      e_lambda v (ord_tuple m).
Proof.
have ho := orthonormalisation_orthonormal hv.
have hvi := @orthonormal_independent R V B hB (Finite.clone 'I_m _) v ho.
have hx := @independent_product_nonzero R h2 V m u hu.
have ht i : FedererSimple.T (e_lambda u (ord_tuple m)) (v i).
  apply: product_associated_span.
  apply: (proj2 (@orthonormalisation_span R V B m u v hv (v i))).
  exact: (@finite_span_generator R V m v i).
have [c [hc he]] := @full_degree_factor R h2 V m (e_lambda u (ord_tuple m)) v hvi ht hx.
have hd := @exterior_inner_triangular R h2 V B hB m u v
  (@gram_schmidt_triangular R V B hB m u v hv).
have hunit : exterior_inner_form h2 hB (e_lambda v (ord_tuple m)) (e_lambda v (ord_tuple m)) = 1.
  by rewrite -exterior_norm_square (orthonormal_product_unit_norm h2 hB ho) expr1n.
rewrite he (bilZl (exterior_inner_form_bilinear h2 hB m)) hunit in hd.
change (c * 1 = foldr ( *%R) 1 [seq B (u i) (v i) | i <- enum 'I_m]) in hd; rewrite mulr1 in hd.
by rewrite he hd.
Qed.

(** Source for [gram_schmidt_exterior_norm]: Federer
    1.7.5, p. 32, the norm of the product is the absolute
    product of the Gram-Schmidt diagonal coefficients. *)
Theorem gram_schmidt_exterior_norm :
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) =
    `|foldr ( *%R) 1 [seq B (u i) (v i) | i <- enum 'I_m]|.
Proof.
by rewrite gram_schmidt_exterior_factor exterior_norm_scale
  (orthonormal_product_unit_norm h2 hB (orthonormalisation_orthonormal hv)) mulr1.
Qed.
End Factor.
