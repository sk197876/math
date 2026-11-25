(** Federer (1969), 1.10.2, p. 45: products of normalized monomial
    coordinates. This supporting proof uses the divided diagonal of 1.9.4 to
    calculate the pairings that. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded Hom HomogeneousHom BoundedHom LinearBasis
  ScalarCoefficients Convolution SymmetricAlgebra SymmetricGrading SymmetricMonomials
  SymmetricMultiIndices SymmetricMonomialBasis SymmetricDividedMonomials
  SymmetricExponentBox SymmetricMultiIndexAddition SymmetricBoxKronecker
  SymmetricDiagonal SymmetricDiagonalMonomials SymmetricFormSum SymmetricFormProduct
  SymmetricMonomialCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Products.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation M := (symmetric_coordinate_full_form he).

(** Source for [symmetric_coordinate_product_divided]: Federer
    1.10.2, p. 45, supporting normalized pairing: the product
    of the alpha and beta coordinates detects precisely exponent alpha+beta. *)
Lemma symmetric_coordinate_product_divided a b g :
  symmetric_forms_product (scalar_bilinear K) (M a) (M b)
    (symmetric_divided_monomial e g) =
    if g == symmetric_multi_add a b then 1 else 0.
Proof.
rewrite symmetric_forms_productE (symmetric_diagonal_divided_monomial_box h0) linear_sum.
transitivity (\sum_(c : symmetric_exponent_box g)
  (if symmetric_exponent_box_index g c == a then (1 : K) else 0) *
  (if symmetric_multi_difference g (symmetric_exponent_box_index g c) == b then 1 else 0)).
- apply: eq_bigr=> c _.
  rewrite /symmetric_diagonal_monomial_term paired_tensorE.
  by rewrite !(@symmetric_coordinate_divided_monomial K V n e he h0).
- exact: symmetric_box_kronecker.
Qed.

(** Source for [symmetric_coordinate_product]: Federer 1.10.2,
    p. 45, supporting multiplication law: normalized monomial
    coordinates multiply by adding their exponent tuples. Their later
    identification with products of one-forms uses this identity. *)
Theorem symmetric_coordinate_product a b :
  symmetric_forms_product (scalar_bilinear K) (M a) (M b) = M (symmetric_multi_add a b).
Proof.
apply: hom_finite_ext=> x.
apply: (basis_linear_ext (proj1 (symmetric_monomials_basis he))
  (hom_as_linear (symmetric_forms_product (scalar_bilinear K) (M a) (M b)))
  (hom_as_linear (M (symmetric_multi_add a b)))) x=> g.
have hg : symmetric_monomial e g =
    ((symmetric_multi_factorial g)%:R : K) *: symmetric_divided_monomial e g.
  have hn : ((symmetric_multi_factorial g)%:R : K) != 0 :=
    @symmetric_multi_factorial_nonzero K h0 n g.
  by rewrite /symmetric_divided_monomial scalerA (mulfV hn) scale1r.
rewrite hg linearZ [RHS]linearZ.
change ((symmetric_multi_factorial g)%:R *
  symmetric_forms_product (scalar_bilinear K) (M a) (M b) (symmetric_divided_monomial e g) =
  (symmetric_multi_factorial g)%:R * M (symmetric_multi_add a b) (symmetric_divided_monomial e g)).
by rewrite symmetric_coordinate_product_divided (@symmetric_coordinate_divided_monomial K V n e he h0).
Qed.
End Products.
