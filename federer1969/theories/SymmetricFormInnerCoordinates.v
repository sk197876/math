(** Federer (1969), 1.10.6, p. 49: the sum-of-squares formula in the
    normalized monomial basis. The subsequent form-norm formula is
    Federer's. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom InnerProductUP InnerNorm LinearBasis FiniteOrdinalBasis
  OrthonormalFamilies InnerSymmetric InnerSymmetricPositivity InnerSymmetricBasis
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricForms SymmetricFormIsomorphism SymmetricPairing SymmetricNormalizedMonomials
  SymmetricFormInner HomInner HomInnerCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable k : nat.
Variable e : 'I_k -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable m : nat.

(** Source for [symmetric_form_inner_basis_independent]: Federer 1.10.6,
    pp. 48-49, supporting intrinsicness: the auxiliary basis used
    in the Hom construction does not change the inner product. *)
Theorem symmetric_form_inner_basis_independent (f g : S_m V W m) :
  symmetric_form_inner hB hC hb m f g = symmetric_form_inner hB hC he m f g.
Proof.
rewrite !symmetric_form_innerE.
exact: hom_inner_basis_independent.
Qed.

(** Source for [symmetric_form_inner_orthonormal_sum]: Federer 1.10.6,
    p. 49, the inner product underlying the first norm formula.
    In words: sum the coefficient inner products of evaluations on the
    normalized monomial basis. The coefficient space may be infinite dimensional. *)
Theorem symmetric_form_inner_orthonormal_sum (f g : S_m V W m) :
  symmetric_form_inner hB hC hb m f g =
    \sum_(a : symmetric_indices k m)
      C (symmetric_pairing (symmetric_normalized_monomial e a) f)
        (symmetric_pairing (symmetric_normalized_monomial e a) g).
Proof.
rewrite symmetric_form_innerE.
have hs := @hom_inner_orthonormal_sum R (symmetric_power V m) W
  _ C (@symmetric_inner_productP R V B hB m) hC _ _
  (finite_ordinal_basis (symmetric_normalized_monomial_basis hb m)) _ _
  (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)).
have ho' : orthonormal_family (@symmetric_inner_form R V B hB m)
    (fun i : 'I_#|{:symmetric_indices k m}| => symmetric_normalized_monomial e (enum_val i)).
  move=> i j; rewrite (symmetric_orthonormal_family hB ho).
  by rewrite (inj_eq (@enum_val_inj (symmetric_indices k m) predT)).
rewrite (hs ho').
rewrite /symmetric_pairing.
by rewrite (big_enum_val (fun a : symmetric_indices k m =>
  C (sform_to_hom f (symmetric_normalized_monomial e a))
    (sform_to_hom g (symmetric_normalized_monomial e a)))).
Qed.

(** Source for [symmetric_form_norm_square_sum]: Federer 1.10.6,
    p. 49, the first displayed norm formula. In words: squared
    length of a form is the sum of squared lengths of its values
    on normalized monomials, including degree zero and zero dimension. *)
Theorem symmetric_form_norm_square_sum (f : S_m V W m) :
  (symmetric_form_norm hB hC hb m f)^+2 =
    \sum_(a : symmetric_indices k m)
      (inner_norm hC (symmetric_pairing (symmetric_normalized_monomial e a) f))^+2.
Proof.
rewrite inner_norm_sqr (symmetric_form_inner_orthonormal_sum f f).
apply: eq_bigr=> a _; exact: esym (inner_norm_sqr hC _).
Qed.
End Coordinates.
