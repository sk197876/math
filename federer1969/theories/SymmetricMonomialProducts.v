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

(** Source for [symmetric_monomial_word_add]: Federer 1.10.3,
    p. 45, supporting exponent calculation: the word for alpha+beta
    is a permutation of the concatenated words for alpha and beta. *)
Lemma symmetric_monomial_word_add n (a b : symmetric_multi_index n) :
  perm_eq (symmetric_monomial_word idfun a ++ symmetric_monomial_word idfun b)
    (symmetric_monomial_word idfun (symmetric_multi_add a b)).
Proof.
rewrite /perm_eq; apply/allP=> i _; apply/eqP.
have hc g : count_mem i (symmetric_monomial_word idfun g) = g i.
  have h := congr1 (fun z : symmetric_multi_index n => z i)
    (symmetric_exponent_word_count_monomial g).
  by move: h; rewrite /symmetric_exponent_word_count ffunE.
by rewrite count_cat !hc symmetric_multi_addE.
Qed.

(** Source for [symmetric_monomial_product]: Federer 1.10.3,
    p. 45, supporting identity e^alpha e^beta=e^(alpha+beta).
    This holds for any vector family, with no basis assumption. *)
Lemma symmetric_monomial_product (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) (a b : symmetric_multi_index n) :
  symmetric_product (symmetric_monomial e a) (symmetric_monomial e b) =
    symmetric_monomial e (symmetric_multi_add a b).
Proof.
rewrite /symmetric_monomial symmetric_word_cat.
apply: symmetric_word_permutation.
have h := perm_map e (symmetric_monomial_word_add a b).
by rewrite map_cat !symmetric_monomial_word_map in h.
Qed.

(** Source for [symmetric_multi_le]: Federer 1.10.3, p. 45,
    the condition alpha<=beta in the two displayed formulas means
    the inequality in every coordinate. *)
Definition symmetric_multi_le n (a b : symmetric_multi_index n) :=
  [forall i, (a i <= b i)%N].

(** Source for [symmetric_multi_add_eq_difference]: Federer
    1.10.3, p. 45, supporting equivalence used for the monomial
    coordinates: gamma+alpha=beta iff alpha<=beta and gamma=beta-alpha. *)
Lemma symmetric_multi_add_eq_difference n (g a b : symmetric_multi_index n) :
  (symmetric_multi_add g a == b) =
    (symmetric_multi_le a b && (g == symmetric_multi_difference b a)).
Proof.
apply/idP/idP.
- move/eqP=> <-; apply/andP; split.
  + apply/forallP=> i; by rewrite symmetric_multi_addE leq_addl.
  + apply/eqP; symmetry; rewrite symmetric_multi_addC.
    exact: symmetric_multi_difference_addl.
- move/andP=> [/forallP hab /eqP ->]; apply/eqP.
  rewrite symmetric_multi_addC; exact: symmetric_multi_add_difference.
Qed.
