(** Federer (1969), 1.10.5, p. 48, first inequality in the final weighted
    polynomial display. The coordinate identity is 1.10.4, p. 47. The family
    need not be a basis for this estimate, and the coefficient space may be
    arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom SymmetricMultiIndices SymmetricIndexBounds
  SymmetricDividedMonomials SymmetricForms SymmetricFormExtension
  HomogeneousPolynomialFunctions PolynomialCoordinates SymmetricMonomialTuples RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_factor_coordinates]: Federer
    1.10.5, p. 48, the coordinate formula with t^alpha/alpha!
    separated from the form value on the repeated-factor tuple. *)
Lemma homogeneous_polynomial_factor_coordinates (K : fieldType)
    (h0 : [pchar K] =i pred0) (V W : lmodType K) n (v : 'I_n -> V)
    (t : 'I_n -> K) m (f : S_m V W m) :
  sform_polynomial_value f (\sum_i t i *: v i) =
    \sum_(a : symmetric_indices n m)
      (symmetric_scalar_monomial t (symmetric_indices_unbound a) /
        (symmetric_multi_factorial (symmetric_indices_unbound a))%:R) *:
      f (symmetric_monomial_tuple v a).
Proof.
rewrite (homogeneous_polynomial_coordinates h0); apply: eq_bigr=> a _.
rewrite /symmetric_divided_monomial linearZ scalerA.
change ((symmetric_scalar_monomial t (symmetric_indices_unbound a) /
    (symmetric_multi_factorial (symmetric_indices_unbound a))%:R) *:
  sform_homogeneous f (SymmetricMonomials.symmetric_monomial v (symmetric_indices_unbound a)) =
  (symmetric_scalar_monomial t (symmetric_indices_unbound a) /
    (symmetric_multi_factorial (symmetric_indices_unbound a))%:R) *:
  f (symmetric_monomial_tuple v a)).
by rewrite symmetric_monomial_form_value.
Qed.

(** Source for [homogeneous_polynomial_coefficient_norm_bound]:
    Federer 1.10.5, p. 48, the first inequality of the final
    display: |P(sum t_j v_j)| is at most the sum of
    |t^alpha/alpha!| times |<v^alpha,phi>|. No input-norm
    hypothesis is needed for this triangle-inequality step. *)
Theorem homogeneous_polynomial_coefficient_norm_bound (R : realType)
    (V W : lmodType R) (NW : W -> R) (hW : is_real_seminorm NW)
    n (v : 'I_n -> V) (t : 'I_n -> R) m (f : S_m V W m) :
  NW (sform_polynomial_value f (\sum_i t i *: v i)) <=
    \sum_(a : symmetric_indices n m)
      `|symmetric_scalar_monomial t (symmetric_indices_unbound a) /
        (symmetric_multi_factorial (symmetric_indices_unbound a))%:R| *
      NW (f (symmetric_monomial_tuple v a)).
Proof.
rewrite (homogeneous_polynomial_factor_coordinates (@pchar_num R)).
apply: le_trans (real_seminorm_sum hW _) _.
apply: ler_sum=> a _; by rewrite (real_seminorm_scale hW).
Qed.
