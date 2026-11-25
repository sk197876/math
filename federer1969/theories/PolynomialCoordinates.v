(** Federer (1969), 1.10.4, p. 47, final displayed coordinate expansion. The
    formula itself holds for any finite family of vectors; a basis is needed
    only for unique coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom HomogeneousHom BoundedHom Graded GradedSums
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricDividedMonomials SymmetricMultinomial
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  PolynomialFunctions PolynomialRepresentations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables V W : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable t : 'I_n -> K.

(** Source for [homogeneous_polynomial_coordinates]: Federer
    1.10.4, p. 47, the degree-m summand in the final display.
    Apply the homogeneous form to the weighted multinomial expansion
    from 1.9.3, p. 42. No basis hypothesis is needed for this identity. *)
Theorem homogeneous_polynomial_coordinates m (f : S_m V W m) :
  sform_polynomial_value f (\sum_i t i *: e i) =
    \sum_(a : symmetric_indices n m)
      symmetric_scalar_monomial t (symmetric_indices_unbound a) *:
        sform_homogeneous f (symmetric_divided_monomial e (symmetric_indices_unbound a)).
Proof.
rewrite /sform_polynomial_value (symmetric_weighted_multinomial h0) linear_sum.
by apply: eq_bigr=> a _; rewrite linearZ.
Qed.

(** Source for [symmetric_polynomial_coordinates]: Federer
    1.10.4, p. 47, final displayed sum over degrees and Xi(n,m).
    This version uses any finite upper bound on the coefficient support. *)
Theorem symmetric_polynomial_coordinates (f : S_star V W) N :
  grade_bounded (S_star_grading V W) f N ->
  symmetric_polynomial_value f (\sum_i t i *: e i) =
    \sum_(m < N) \sum_(a : symmetric_indices n m)
      symmetric_scalar_monomial t (symmetric_indices_unbound a) *:
        sform_homogeneous (sform_component m f)
          (symmetric_divided_monomial e (symmetric_indices_unbound a)).
Proof.
move=> hN; rewrite (symmetric_polynomial_value_bound _ hN).
apply: eq_bigr=> m _; exact: homogeneous_polynomial_coordinates.
Qed.

(** Source for [polynomial_coordinates]: Federer 1.10.4,
    p. 47, final display for an actual polynomial function,
    summed through its intrinsic degree, including the zero polynomial. *)
Theorem polynomial_coordinates (P : PolynomialFunction V W) :
  P (\sum_i t i *: e i) =
    \sum_(m < (polynomial_degree P).+1) \sum_(a : symmetric_indices n m)
      symmetric_scalar_monomial t (symmetric_indices_unbound a) *:
        sform_homogeneous (sform_component m (polynomial_to_forms P))
          (symmetric_divided_monomial e (symmetric_indices_unbound a)).
Proof.
rewrite polynomial_degree_representation.
apply: eq_bigr=> m _; exact: homogeneous_polynomial_coordinates.
Qed.
End Coordinates.
