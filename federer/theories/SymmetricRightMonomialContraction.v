(** Federer (1969), 1.10.3, p. 45: the two monomial interior formulas and
    their zero cases. The coefficient computations below prove Federer's
    displayed formulas using the monomial bases and diagonal already
    established in 1.9. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear Graded Hom HomogeneousHom BoundedHom
  LinearBasis BasisInterpolation ScalarCoefficients ScalarTensorContraction
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricMonomials
  SymmetricExponentBox SymmetricMultiIndexAddition SymmetricExponentWords
  SymmetricMonomialBasis SymmetricDividedMonomials SymmetricDiagonal
  SymmetricDiagonalMonomials SymmetricForms SymmetricFormSum SymmetricFormProduct
  SymmetricMonomialCoordinates SymmetricRightInteriorHom SymmetricLeftInteriorHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

From Federer Require Import SymmetricMonomialProducts.
Section MonomialContraction.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation C := (symmetric_monomial_coordinate he).

(** Source for [symmetric_right_monomial_coordinate]: Federer
    1.10.3, p. 45, first displayed monomial formula in coordinate
    form. The coordinate C_beta equals omega^beta/beta! in characteristic
    zero; contraction by e^alpha subtracts alpha when alpha<=beta,
    and otherwise is the zero functional. *)
Theorem symmetric_right_monomial_coordinate a b :
  symmetric_right_interior_hom (symmetric_monomial e a) (C b) =
    if symmetric_multi_le a b then C (symmetric_multi_difference b a) else 0.
Proof.
apply: hom_ext=> x.
apply: (basis_linear_ext (proj1 (symmetric_monomials_basis he))
  (hom_as_linear (symmetric_right_interior_hom (symmetric_monomial e a) (C b)))
  (hom_as_linear (if symmetric_multi_le a b then C (symmetric_multi_difference b a) else 0))) x=> g.
change (symmetric_right_interior_hom (symmetric_monomial e a) (C b) (symmetric_monomial e g) =
  (if symmetric_multi_le a b then C (symmetric_multi_difference b a) else 0)
    (symmetric_monomial e g)).
rewrite symmetric_right_interior_homE symmetric_monomial_product
  symmetric_monomial_coordinateE symmetric_multi_add_eq_difference.
case: (symmetric_multi_le a b)=> /=.
- exact: esym (symmetric_monomial_coordinateE he _ _).
- by [].
Qed.
End MonomialContraction.
