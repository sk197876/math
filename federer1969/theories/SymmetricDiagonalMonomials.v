(** Federer (1969), 1.9.4, p. 43: the divided monomial diagonal formula,
    first indexed directly by all beta<=alpha. The coordinate-product
    expansion is equivalent to the printed grouping by p=sum beta. No basis
    hypothesis is needed for this identity. Characteristic zero justifies
    factorial division. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded SymmetricAlgebra SymmetricGrading SymmetricDirectSum
  SymmetricDiagonal SymmetricDiagonalPowers SymmetricMultiIndices SymmetricExponentBox
  SymmetricMonomials SymmetricDividedMonomials SymmetricMonomialFactors.
From Federer Require Import UnitalGradedTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DiagonalMonomials.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation EG := (unital_graded_view E).
Local Notation T := (unital_graded_tensor E E false).
Local Notation D := (symmetric_diagonal V).
Local Notation mu := (alg_mul T).

(** Source for [symmetric_diagonal_monomial_term]: Federer
    1.9.4, p. 43, the tensor of the divided monomials
    e^beta/beta! and e^(alpha-beta)/(alpha-beta)!. *)
Definition symmetric_diagonal_monomial_term n (v : 'I_n -> V)
    (a b : symmetric_multi_index n) : T :=
  tensor_inj (symmetric_divided_monomial v b)
    (symmetric_divided_monomial v (symmetric_multi_difference a b)).

(** Source for [symmetric_diagonal_monomial_term_cons]: Federer
    1.9.4, p. 43, supporting factorisation of a summand
    into its first coordinate and its remaining coordinates. *)
Lemma symmetric_diagonal_monomial_term_cons n (v : 'I_n.+1 -> V)
    k l (a b : symmetric_multi_index n) :
  symmetric_diagonal_monomial_term v (symmetric_multi_cons k a) (symmetric_multi_cons l b) =
    mu (tensor_inj (symmetric_divided_vector_power (v ord0) l)
          (symmetric_divided_vector_power (v ord0) (k-l)))
       (symmetric_diagonal_monomial_term (fun i => v (lift ord0 i)) a b).
Proof.
have ht (x y z w : E) : mu (tensor_inj x y) (tensor_inj z w) =
    tensor_inj (symmetric_product x z) (symmetric_product y w).
  exact: (@ordinary_tensor_mulE K EG EG x y z w).
by rewrite /symmetric_diagonal_monomial_term symmetric_multi_difference_cons
  !symmetric_divided_monomial_cons ht.
Qed.

(** Source for [symmetric_diagonal_divided_monomial_box]:
    Federer 1.9.4, p. 43, the divided monomial diagonal
    formula enumerating beta<=alpha by the finite product of its
    coordinate ranges. The subsequent reindexing groups by total degree. *)
Theorem symmetric_diagonal_divided_monomial_box n (v : 'I_n -> V) (a : symmetric_multi_index n) :
  D (symmetric_divided_monomial v a) =
    \sum_(b : symmetric_exponent_box a)
      symmetric_diagonal_monomial_term v a (symmetric_exponent_box_index a b).
Proof.
elim: n v a=> [v a|n ih v a].
- rewrite (big_pred1 tt); last by case.
  rewrite /symmetric_diagonal_monomial_term /symmetric_divided_monomial
    /symmetric_monomial /symmetric_monomial_word /symmetric_multi_factorial
    !enum_ord0 !big_ord0 /= !invr1 !scale1r.
  exact: (algebra_map_one D).
- have ha := symmetric_multi_head_tail a.
  rewrite -{1}ha symmetric_divided_monomial_cons algebra_map_mul
    (symmetric_diagonal_divided_power h0) ih.
  rewrite (big_morph (fun x => mu x _) (fun x y => bilDl (alg_bilinear T) x y _)
    (bil0l (alg_bilinear T) _)).
  under eq_bigr do rewrite (big_morph (mu _) (bilDr (alg_bilinear T) _) (bil0r (alg_bilinear T) _)).
  rewrite pair_bigA; apply: eq_bigr=> [[k b]] _.
  have hh := @symmetric_diagonal_monomial_term_cons n v
    (symmetric_multi_head a) (val k) (symmetric_multi_tail a)
    (symmetric_exponent_box_index (symmetric_multi_tail a) b).
  rewrite ha in hh.
  exact: esym hh.
Qed.
End DiagonalMonomials.
