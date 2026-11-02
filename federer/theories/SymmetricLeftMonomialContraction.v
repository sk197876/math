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
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation M := (symmetric_coordinate_full_form he).

(** Source for [symmetric_left_monomial_coordinate]: Federer
    1.10.3, p. 45, second displayed formula. Contraction of
    e^beta/beta! by the normalized coordinate M_alpha, which is
    omega^alpha, gives e^(beta-alpha)/(beta-alpha)! if alpha<=beta
    and zero otherwise. The proof selects the sole surviving term
    of the divided-monomial diagonal from 1.9.4. *)
Theorem symmetric_left_monomial_coordinate a b :
  symmetric_left_interior_hom (symmetric_divided_monomial e b) (M a) =
    if symmetric_multi_le a b then symmetric_divided_monomial e (symmetric_multi_difference b a)
    else 0.
Proof.
rewrite /symmetric_left_interior_hom
  (symmetric_diagonal_divided_monomial_box h0) linear_sum.
have ht (c : symmetric_exponent_box b) :
  @contract_tensor K (symmetric_space V) (symmetric_space V) (M a) (symmetric_diagonal_monomial_term e b (symmetric_exponent_box_index b c)) =
    (if symmetric_exponent_box_index b c == a then (1 : K) else 0) *:
      symmetric_divided_monomial e (symmetric_multi_difference b (symmetric_exponent_box_index b c)).
  by rewrite /symmetric_diagonal_monomial_term contract_tensorE
    (@symmetric_coordinate_divided_monomial K V n e he h0).
under eq_bigr do rewrite ht.
case hle: (symmetric_multi_le a b).
- have hab : forall i, (a i <= b i)%N by move/forallP: hle.
  have [c hc] := symmetric_exponent_box_surjective hab.
  rewrite (bigD1 c) //= hc eqxx scale1r.
  have hz : (\sum_(d : symmetric_exponent_box b | d != c)
    (if symmetric_exponent_box_index b d == a then (1 : K) else 0) *:
      symmetric_divided_monomial e (symmetric_multi_difference b (symmetric_exponent_box_index b d))) = 0.
    apply: big1=> d hd.
    have hda : symmetric_exponent_box_index b d != a.
      apply/eqP=> hda.
      have hdc : d=c := symmetric_exponent_box_injective (eq_trans hda (esym hc)).
      by move: hd; rewrite hdc eqxx.
    by rewrite (negbTE hda) scale0r.
  by rewrite hz addr0.
- apply: big1=> c _.
  have hca : symmetric_exponent_box_index b c != a.
    apply/eqP=> hca.
    have hab : symmetric_multi_le a b.
      apply/forallP=> i; rewrite -hca; exact: symmetric_exponent_box_bound.
    by move: hab; rewrite hle.
  by rewrite (negbTE hca) scale0r.
Qed.
End MonomialContraction.
