(** Federer (1969), 1.9.2, p. 42: identifying the recursively constructed
    basis with the displayed products e^alpha. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import GradedBasis Graded LinearBasis FiniteCoordinates
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricMultiIndices
  SymmetricLineBasis SymmetricCoordinateSplit SymmetricCoordinateBasis SymmetricMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinateMonomials.
Variable K : fieldType.

(** Source for [symmetric_coordinate_monomialE]: Federer 1.9.2,
    p. 42, the dimension induction gives exactly the monomial
    formed by repeating each coordinate basis vector alpha_i times. *)
Lemma symmetric_coordinate_monomialE n (a : symmetric_multi_index n) :
  symmetric_coordinate_monomial K a = symmetric_monomial (@coordinate_basis K n) a.
Proof.
elim: n a => [a|n ih a].
- by rewrite /symmetric_monomial /symmetric_monomial_word enum_ord0.
- change (symmetric_coordinate_join K n
    (tensor_inj (symmetric_line_power K (symmetric_multi_head a))
      (symmetric_coordinate_monomial K (symmetric_multi_tail a))) =
      symmetric_monomial (@coordinate_basis K n.+1) a).
  rewrite symmetric_coordinate_joinE ih.
  rewrite /symmetric_line_power symmetric_algebra_map_word map_nseq.
  have hh : (GRing.Linear.clone _ _ _ _ (@coordinate_head_inclusion K n) _) 1 =
      coordinate_basis K ord0 := @coordinate_head_basis K n.
  rewrite hh.
  rewrite symmetric_monomial_natural /symmetric_monomial symmetric_word_cat.
  congr 1 (symmetric_word _).
  rewrite /symmetric_monomial_word enum_ordSl /= -map_comp.
  congr (_ ++ _).
  congr 1 (flatten _); apply: eq_map=> i.
  by rewrite /symmetric_multi_tail ffunE /= coordinate_tail_basis.
Qed.

(** Source for [symmetric_coordinate_monomials_basis]: Federer
    1.9.2, p. 42, all monomials in the coordinate basis form a
    basis of the symmetric algebra, with degree equal to total exponent. *)
Theorem symmetric_coordinate_monomials_basis n :
  is_graded_basis (symmetric_grading (coordinate_space K n))
    (symmetric_monomial (@coordinate_basis K n)) (@symmetric_multi_degree n).
Proof.
have [hb hg] := symmetric_coordinate_monomial_basis K n; split.
- exact: basis_congr (@symmetric_coordinate_monomialE n) hb.
- exact: symmetric_monomial_homogeneous.
Qed.
End CoordinateMonomials.
