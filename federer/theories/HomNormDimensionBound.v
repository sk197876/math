(** Federer (1969), 1.7.9, p. 35: the norm of a map as a tensor is at most
    the square root of the source dimension times its operator norm.
    Dimension zero is included. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  HomInner HomInnerCoordinates Hom LinearBasis OperatorNormUP
  GramSchmidt OrthonormalisationUP OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hom_norm_le_dimension_operator_norm]: Federer
    1.7.9, p. 35, second printed inequality: |f| is at most
    sqrt(n) times its operator norm, for n the source dimension. *)
Theorem hom_norm_le_dimension_operator_norm (R : rcfType)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : Hom V W) L :
  is_operator_norm hB hC (hom_as_linear f) L ->
  hom_norm hB hC hb f <= Num.sqrt n%:R * L.
Proof.
move=> hL.
have hLn := operator_norm_nonnegative hL.
have [e [he ho]] := orthonormal_basis_exists hB hb.
have horth := orthonormalisation_orthonormal ho.
rewrite -(ler_sqr (inner_norm_nonnegative _ _) (mulr_ge0 (sqrtr_ge0 _) hLn)).
rewrite exprMn sqr_sqrtr ?ler0n // inner_norm_sqr.
rewrite (@hom_inner_orthonormal_sum R V W B C hB hC n b hb n e he horth f f).
have hsum : (\sum_i C (f (e i)) (f (e i))) <= \sum_(i : 'I_n) L^+2.
  apply: ler_sum => i _; rewrite -(inner_norm_sqr hC).
  rewrite (ler_sqr (inner_norm_nonnegative hC _) hLn).
  have hu : inner_norm hB (e i) <= 1 by rewrite (orthonormal_norm1 hB horth).
  exact (@operator_norm_unit_bound R V W B C hB hC (hom_as_linear f) L hL (e i) hu).
by rewrite sumr_const card_ord -mulr_natl in hsum.
Qed.
