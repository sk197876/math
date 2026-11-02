(** Federer (1969), 1.7.5, p. 32: the residual-product identity and the
    displayed product of vi dot wi. Only the abstract residual-family
    specification is used; dependent families are included. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorTriangular
  ExteriorNorm InnerNorm ExteriorHadamardBound OrthogonalResidualFamily
  TriangularProductChange FinitePrefixes FiniteSpans FiniteSpanSpace
  ModuleQuotient ExteriorGrading FiniteExteriorPowers ExteriorExpansion Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Products.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variables v u w : 'I_n -> V.
Hypothesis hr : is_orthogonal_residual_family B v u w.

(** Source for [orthogonal_residual_product_identity]: Federer
    1.7.5, p. 32, the exterior products of the original
    vectors and their residuals coincide, including dependent families. *)
Theorem orthogonal_residual_product_identity :
  e_lambda v (ord_tuple n) = e_lambda w (ord_tuple n).
Proof.
apply: triangular_exterior_product_change => i.
have he : v i-w i = u i by rewrite (residual_family_decomposition hr i) addrK.
rewrite he; exact (@residual_family_projection R V B n v u w hr i).
Qed.

(** Source for [orthogonal_residual_triangular]: Federer
    1.7.5, p. 32, vj dot wi vanishes when j precedes i,
    so the permutation sum reduces to its diagonal term. *)
Lemma orthogonal_residual_triangular (i j : 'I_n) : (j < i)%N -> B (v j) (w i) = 0.
Proof.
move=> hj; rewrite (inner_symmetric hB).
apply: (@residual_family_orthogonal R V B n v u w hr i (v j)).
pose a : 'I_i := Ordinal hj.
have ha : widen_ord (ltnW (ltn_ord i)) a = j by apply: val_inj.
rewrite -ha; exact: (@finite_span_generator R V i (family_prefix (ltnW (ltn_ord i)) v) a).
Qed.

(** Source for [orthogonal_residual_diagonal]: Federer
    1.7.5, p. 32, vi dot wi equals wi dot wi because
    the projected part ui is orthogonal to the residual wi. *)
Lemma orthogonal_residual_diagonal i : B (v i) (w i) = B (w i) (w i).
Proof.
have hz := @residual_family_orthogonal R V B n v u w hr i (u i)
  (@residual_family_projection R V B n v u w hr i).
by rewrite (residual_family_decomposition hr i) (bilDl (inner_bilinear hB))
  (inner_symmetric hB (u i) (w i)) hz add0r.
Qed.

(** Source for [orthogonal_residual_norm_square]: Federer
    1.7.5, p. 32, the first equality in the displayed
    residual calculation: the squared product norm is the product
    of vi dot wi. *)
Theorem orthogonal_residual_norm_square :
  exterior_norm h2 hB (e_lambda v (ord_tuple n))^+2 = \prod_i B (v i) (w i).
Proof.
rewrite exterior_norm_square {2}orthogonal_residual_product_identity
  (@exterior_inner_triangular R h2 V B hB n v w orthogonal_residual_triangular)
  foldrE big_map /= product_index_enum; by [].
Qed.

(** Source for [orthogonal_residual_product_bound]: Federer
    1.7.5, p. 32, the full displayed chain: the squared
    norm equals the product of vi dot wi and this is at most
    the product of vi dot vi. *)
Theorem orthogonal_residual_product_bound :
  exterior_norm h2 hB (e_lambda v (ord_tuple n))^+2 = (\prod_i B (v i) (w i)) /\
    (\prod_i B (v i) (w i)) <= (\prod_i B (v i) (v i)).
Proof.
split; first exact: orthogonal_residual_norm_square.
rewrite -orthogonal_residual_norm_square.
have hn : 0 <= \prod_i inner_norm hB (v i).
  apply: prodr_ge0 => i _; exact: inner_norm_nonnegative.
have hh := @exterior_product_norm_bound R h2 V B hB n v.
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hB _) hn) -prodrXl in hh.
have hs : (\prod_i (inner_norm hB (v i))^+2) = \prod_i B (v i) (v i).
  apply: eq_bigr => i _; exact: inner_norm_sqr.
by rewrite hs in hh.
Qed.
End Products.
