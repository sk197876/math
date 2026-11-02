(** Federer (1969), 1.10.5, p. 47, the normalized orthonormal monomials. The
    calculation is made through a finite coordinate space but does not
    require that its image span the ambient inner-product space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP Graded GradedComponents
  Hom BoundedHom LinearBasis InnerProductUP OrthonormalFamilies
  InnerSymmetricPolarity InnerSymmetric InnerSymmetricMonomials
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricLowPowers
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricMonomialBasis
  SymmetricDividedMonomials SymmetricForms SymmetricFormDual SymmetricPairing
  SymmetricDualMonomialProducts SymmetricCoordinateDualBasis
  SymmetricMonomialNaturality SymmetricBiorthogonalMonomials SymmetricNormalizedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_finite_monomial_map]: Federer 1.10.5,
    p. 47, supporting finite-dimensional reduction of the monomial
    calculation. The induced map carries each typed monomial to the
    monomial in the images of its generating family. *)
Lemma symmetric_finite_monomial_map (K : fieldType) (U V : lmodType K)
    n (e : 'I_n -> U) (F : {linear U -> V}) m (a : symmetric_indices n m) :
  symmetric_power_map F m (symmetric_finite_monomial e a) =
    symmetric_finite_monomial (F \o e) a.
Proof.
apply: val_inj.
change (symmetric_algebra_map F (symmetric_monomial e (symmetric_indices_unbound a)) =
  symmetric_monomial (F \o e) (symmetric_indices_unbound a)).
exact: symmetric_monomial_natural.
Qed.

Section Gram.
Variable R : realFieldType.
Variables U V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.
Variable F : {linear U -> V}.
Hypothesis ho : orthonormal_family B (F \o e).

(** Source for [symmetric_transport_polarity_dual]: Federer 1.10.5,
    p. 47, supporting identification of the polarities with dual
    coordinate forms on the finite source space. *)
Lemma symmetric_transport_polarity_dual i j :
  symmetric_pairing (symmetric_first_inclusion U (e j))
    (S_m_dual F (inner_symmetric_polarity hB (F (e i)))) = if j == i then 1 else 0.
Proof.
rewrite S_m_dual_symmetric_pairing symmetric_first_inclusion_natural inner_symmetric_polarityE.
exact: ho.
Qed.

(** Source for [symmetric_monomial_gram]: Federer 1.10.5,
    p. 47, the Gram matrix before normalization: ordinary monomials
    are orthogonal, with squared length alpha!. The proof uses the
    actual dual products of 1.10.2 and the sealed polarity extension. *)
Theorem symmetric_monomial_gram m (a b : symmetric_indices n m) :
  symmetric_inner_form hB (symmetric_finite_monomial (F \o e) a)
    (symmetric_finite_monomial (F \o e) b) =
    (symmetric_multi_factorial (symmetric_indices_unbound a))%:R *
      (if a == b then 1 else 0).
Proof.
rewrite symmetric_inner_formE.
change (inner_symmetric_extension hB (symmetric_monomial (F \o e) (symmetric_indices_unbound b))
  (symmetric_monomial (F \o e) (symmetric_indices_unbound a)) =
  (symmetric_multi_factorial (symmetric_indices_unbound a))%:R * (if a == b then 1 else 0)).
rewrite inner_symmetric_monomial.
rewrite (@symmetric_ordinary_monomial_pairing_transport R (@pchar_num R)
  U V n e he F (fun i => inner_symmetric_polarity hB (F (e i)))
  symmetric_transport_polarity_dual (symmetric_indices_unbound b) (symmetric_indices_unbound a)).
by rewrite (inj_eq (@symmetric_indices_unbound_injective n m)).
Qed.
End Gram.

Section Normalized.
Variable R : rcfType.
Variables U V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.
Variable F : {linear U -> V}.
Hypothesis ho : orthonormal_family B (F \o e).

(** Source for [symmetric_normalized_monomial_map]: Federer 1.10.5,
    p. 47, supporting transport of the normalized finite basis
    into the ambient space. The scalar normalization commutes with
    the linear induced symmetric-power map. *)
Lemma symmetric_normalized_monomial_map m (a : symmetric_indices n m) :
  symmetric_power_map F m (symmetric_normalized_monomial e a) =
    symmetric_normalized_monomial (F \o e) a.
Proof.
rewrite /symmetric_normalized_monomial linearZ.
change ((symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
  symmetric_power_map F m (symmetric_finite_monomial e a) =
  (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
  symmetric_finite_monomial (F \o e) a).
by rewrite symmetric_finite_monomial_map.
Qed.

(** Source for [symmetric_transported_orthonormal_monomials]: Federer
    1.10.5, p. 47, the first displayed orthonormal-family
    assertion, for the image of a finite basis that is orthonormal
    in the ambient space. No surjectivity of F is assumed. *)
Theorem symmetric_transported_orthonormal_monomials m :
  orthonormal_family (@symmetric_inner_form R V B hB m)
    (fun a : symmetric_indices n m => symmetric_normalized_monomial (F \o e) a).
Proof.
move=> a b; rewrite /symmetric_normalized_monomial
  (bilZl (@symmetric_inner_form_bilinear R V B hB m))
  (bilZr (@symmetric_inner_form_bilinear R V B hB m)).
change ((symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *
  ((symmetric_factorial_root R (symmetric_indices_unbound b))^-1 *
    symmetric_inner_form hB (symmetric_finite_monomial (F \o e) a)
      (symmetric_finite_monomial (F \o e) b)) = if a == b then 1 else 0).
rewrite (@symmetric_monomial_gram R U V B hB n e he F ho m a b).
case hab: (a == b); last by rewrite !mulr0.
move/eqP: hab=> ->.
rewrite mulr1 mulrA -invfM -expr2 symmetric_factorial_root_square mulVf //.
exact: (@symmetric_multi_factorial_nonzero R (@pchar_num R)).
Qed.
End Normalized.
