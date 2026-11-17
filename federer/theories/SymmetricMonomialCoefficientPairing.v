(** Supporting Federer (1969), 3.4.8(5), p. 328:
    convert normalized original derivative evaluation to the
    existing divided-monomial pairing of 1.10.2, p. 45. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom HomogeneousHom BoundedHom GradedComponents
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricPairing
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricDividedMonomials
  SymmetricDividedBasis SymmetricMonomialTuples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_normalized_monomial_form_pairing]: supporting
    exact finite Taylor coefficient for Federer 3.4.8(5), p. 328.
    Dividing the original repeated-argument evaluation by alpha! is
    precisely the original divided-monomial pairing of 1.10.2, p. 45. *)
Lemma symmetric_normalized_monomial_form_pairing (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) k (b:symmetric_indices n k) (phi:S_m X K^o k):
  symmetric_pairing (symmetric_divided_basis_vector e b) phi =
    ((symmetric_multi_factorial (symmetric_indices_unbound b))%:R:K)^-1 *
      phi (symmetric_monomial_tuple e b).
Proof.
rewrite /symmetric_pairing sform_to_homE symmetric_divided_basis_vectorE
  /symmetric_divided_monomial linearZ.
change (((symmetric_multi_factorial (symmetric_indices_unbound b))%:R:K)^-1 *
  sform_homogeneous phi (symmetric_monomial e (symmetric_indices_unbound b)) =
  ((symmetric_multi_factorial (symmetric_indices_unbound b))%:R:K)^-1 *
    phi (symmetric_monomial_tuple e b)).
rewrite symmetric_monomial_form_value.
reflexivity.
Qed.
