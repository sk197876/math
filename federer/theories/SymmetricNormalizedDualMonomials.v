(** Federer (1969), 1.10.6, p. 49: normalized primal and dual monomials form
    dual orthonormal bases. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerSymmetric InnerSymmetricPolarity
  InnerSymmetricBasis InnerSymmetricPositivity SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricPairing SymmetricLowPowers SymmetricMultiIndices
  SymmetricIndexBounds SymmetricMonomialBasis SymmetricNormalizedMonomials
  SymmetricDualMonomialBasis SymmetricPolarityIsomorphism SymmetricPolarityMetric
  SymmetricFormInner ScalarInnerProduct LinearBasis BasisRescaling OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_normalized_dual_monomial]: Federer 1.10.6,
    p. 49, the covector omega^alpha/sqrt(alpha!), formed using
    the actual symmetric product of the supplied one-forms. *)
Definition symmetric_normalized_dual_monomial (R : rcfType) (V : lmodType R)
    n (omega : 'I_n -> S_m V R^o 1) m (a : symmetric_indices n m) : S_m V R^o m :=
  (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
    symmetric_dual_monomial omega a.

Section Normalized.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation omega := (fun i => inner_symmetric_polarity hB (e i)).
Variable m : nat.

(** Source for [symmetric_polarity_normalized_monomial]: Federer 1.10.6,
    p. 49, the normalized vector and covector bases correspond
    under the polarity, since its algebra extension is linear. *)
Lemma symmetric_polarity_normalized_monomial (a : symmetric_indices n m) :
  inner_symmetric_form hB (symmetric_normalized_monomial e a) =
    symmetric_normalized_dual_monomial omega a.
Proof.
rewrite /symmetric_normalized_monomial linearZ.
change ((symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
  inner_symmetric_form hB (symmetric_finite_monomial e a) =
  (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
    symmetric_dual_monomial omega a).
by rewrite symmetric_polarity_monomial.
Qed.

(** Source for [symmetric_normalized_dual_pairing]: Federer 1.10.6,
    p. 49, the two displayed normalized monomial bases are dual. *)
Theorem symmetric_normalized_dual_pairing (a b : symmetric_indices n m) :
  symmetric_pairing (symmetric_normalized_monomial e b)
    (symmetric_normalized_dual_monomial omega a) = if b == a then 1 else 0.
Proof.
rewrite -symmetric_polarity_normalized_monomial.
exact: (@symmetric_orthonormal_family R V B hB n e ho m b a).
Qed.

(** Source for [symmetric_normalized_dual_orthonormal]: Federer 1.10.6,
    p. 49, the displayed normalized dual monomials are orthonormal
    for the scalar form inner product. *)
Theorem symmetric_normalized_dual_orthonormal :
  orthonormal_family (symmetric_form_inner hB (scalar_inner_productP R) he m)
    (@symmetric_normalized_dual_monomial R V n omega m).
Proof.
move=> a b; rewrite -!symmetric_polarity_normalized_monomial symmetric_polarity_isometry.
exact: (@symmetric_orthonormal_family R V B hB n e ho m a b).
Qed.

(** Source for [symmetric_normalized_dual_basis]: Federer 1.10.6,
    p. 49, the normalized covectors form a basis, including
    the empty monomial in degree zero. *)
Theorem symmetric_normalized_dual_basis :
  is_basis (@symmetric_normalized_dual_monomial R V n omega m).
Proof.
have hd i j : symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) =
    if j == i then 1 else 0 by rewrite inner_symmetric_polarityE ho.
apply: (@basis_rescaling R (Choice.clone (symmetric_indices n m) _)
  (S_m V R^o m) (@symmetric_dual_monomial R V n omega m)
  (@symmetric_dual_monomial_basis R V n omega e he (@pchar_num R) hd m)).
move=> a; rewrite invr_eq0.
exact: lt0r_neq0 (symmetric_factorial_root_positive R (symmetric_indices_unbound a)).
Qed.
End Normalized.
