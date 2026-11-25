(** Federer (1969), 1.9.4, p. 43: the displayed divided monomial diagonal
    formula with its original degree grouping. The denominator of the second
    factor is (alpha-beta)!, as in Federer. their following proof uses the
    correct alpha-beta factors. Characteristic zero replaces the real scalar
    field. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP TensorUP TensorProduct SymmetricAlgebra SymmetricDirectSum SymmetricDiagonal
  SymmetricMultiIndices SymmetricIndexBounds SymmetricBoxFibres SymmetricBoxSums
  SymmetricExponentBox SymmetricDividedMonomials SymmetricDiagonalMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [symmetric_diagonal_divided_monomial]: Federer
    1.9.4, p. 43, the displayed formula for the diagonal
    of e^alpha/alpha!: sum over p and beta in Xi(n,p), beta<=alpha,
    of e^beta/beta! tensor e^(alpha-beta)/(alpha-beta)!. The
    identity holds for any vector family, whether or not it is a basis. *)
Theorem symmetric_diagonal_divided_monomial (K : fieldType)
    (h0 : [pchar K] =i pred0) (V : lmodType K) n (e : 'I_n -> V)
    (a : symmetric_multi_index n) :
  symmetric_diagonal V (symmetric_divided_monomial e a) =
    \sum_(p < (symmetric_multi_degree a).+1)
      \sum_(b : symmetric_indices n p | symmetric_subindex a b)
        tensor_inj (symmetric_divided_monomial e (symmetric_indices_unbound b))
          (symmetric_divided_monomial e (symmetric_multi_difference a (symmetric_indices_unbound b))).
Proof.
rewrite (symmetric_diagonal_divided_monomial_box h0) symmetric_box_sum_by_degree.
by [].
Qed.
