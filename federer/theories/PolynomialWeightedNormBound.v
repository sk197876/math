(** Federer (1969), 1.10.5, p. 48, the complete final weighted polynomial
    estimate. The coordinate identity and its triangle estimate are in
    PolynomialCoefficientNorm.v; the scalar multinomial equality is in
    ScalarDividedMultinomial.v. Here each input vector has norm at most one.
    Infinite form norms are allowed, with zero times infinity equal to zero
    in the established order convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricForms HomogeneousPolynomialFunctions SymmetricMonomialTuples
  RealNormUP SymmetricOperatorNormUP SymmetricOperatorNorm ScalarDividedMultinomial
  PolynomialCoefficientNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_monomial_unit_tuple]: Federer 1.10.5,
    p. 48, supporting use of the form norm: repeating vectors
    from a unit-ball family gives an admissible unit tuple. *)
Lemma symmetric_monomial_unit_tuple (R : realType) (V : lmodType R)
    (N : V -> R) n (v : 'I_n -> V) (hv : forall i, N (v i)<=1)
    m (a : symmetric_indices n m) : symmetric_form_unit_tuple N (symmetric_monomial_tuple v a).
Proof.
move=> i; have hi := mem_tnth i (symmetric_monomial_tuple v a).
have [j hj] := symmetric_monomial_word_member hi.
rewrite hj; exact: hv.
Qed.

(** Source for [homogeneous_polynomial_coefficient_operator_bound]:
    Federer 1.10.5, p. 48, the second inequality in the final
    display, together with its multinomial equality. The sum of
    coefficient-weighted form values is at most ||phi|| times
    (sum |t_j|)^m/m!. *)
Theorem homogeneous_polynomial_coefficient_operator_bound (R : realType)
    (V W : lmodType R) (NV : V -> R) (NW : W -> R)
    (hV : is_real_seminorm NV) n (v : 'I_n -> V) (hv : forall i, NV (v i)<=1)
    (t : 'I_n -> R) m (f : S_m V W m) :
  ((\sum_(a : symmetric_indices n m)
      `|symmetric_scalar_monomial t (symmetric_indices_unbound a) /
        (symmetric_multi_factorial (symmetric_indices_unbound a))%:R| *
      NW (f (symmetric_monomial_tuple v a)))%R%:E <=
    symmetric_operator_norm hV NW f *
      (((\sum_i `|t i|)^+m / (m`!)%:R)%R%:E))%E.
Proof.
rewrite -scalar_divided_multinomial_absolute muleC -!sumEFin.
rewrite ge0_sume_distrl; last by move=> a _; rewrite lee_fin normr_ge0.
apply: lee_sum=> a _; rewrite EFinM.
apply: lee_wpmul2l; first by rewrite lee_fin normr_ge0.
apply: symmetric_operator_norm_upper.
exact (@symmetric_monomial_unit_tuple R V NV n v hv m a).
Qed.

(** Source for [homogeneous_polynomial_weighted_norm_bound]:
    Federer 1.10.5, p. 48, the resulting final bound
    |P(sum t_j v_j)| <= ||phi|| (sum |t_j|)^m/m!,
    provided each |v_j|<=1. The preceding lemmas retain the
    intermediate coefficient sum from the printed display. *)
Theorem homogeneous_polynomial_weighted_norm_bound (R : realType)
    (V W : lmodType R) (NV : V -> R) (NW : W -> R)
    (hV : is_real_seminorm NV) (hW : is_real_seminorm NW)
    n (v : 'I_n -> V) (hv : forall i, NV (v i)<=1) (t : 'I_n -> R)
    m (f : S_m V W m) :
  ((NW (sform_polynomial_value f (\sum_i t i *: v i)))%:E <=
    symmetric_operator_norm hV NW f *
      (((\sum_i `|t i|)^+m / (m`!)%:R)%R%:E))%E.
Proof.
apply: le_trans _ (@homogeneous_polynomial_coefficient_operator_bound R V W NV NW hV n v hv t m f).
rewrite lee_fin; exact: homogeneous_polynomial_coefficient_norm_bound.
Qed.
