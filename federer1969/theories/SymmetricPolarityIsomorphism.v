(** Federer (1969), 1.10.6, pp. 48-49: the polarity of 1.10.5 is an
    isomorphism onto the scalar symmetric forms in finite dimension. The
    inverse below follows from those bases and the abstract basis
    interpolation laws, without opening the sealed polarity construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerSymmetric InnerSymmetricPolarity
  InnerSymmetricMonomials SymmetricAlgebra SymmetricGrading GradedComponents
  SymmetricForms SymmetricFormSum SymmetricPairing SymmetricLowPowers
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricMonomialBasis
  SymmetricDualMonomialBasis OrthonormalFamilies LinearBasis IndependentMap
  GramSchmidt OrthonormalisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_polarity_monomial]: Federer 1.10.6,
    p. 49, the corresponding primal and dual monomials are
    images under the polarity described in 1.10.5, p. 47. *)
Lemma symmetric_polarity_monomial (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> V)
    m (a : symmetric_indices n m) :
  inner_symmetric_form hB (symmetric_finite_monomial e a) =
    symmetric_dual_monomial (fun i => inner_symmetric_polarity hB (e i)) a.
Proof.
rewrite /inner_symmetric_form /symmetric_finite_monomial symmetric_monomial_componentE.
by rewrite inner_symmetric_monomial.
Qed.

(** Source for [symmetric_polarity_inverse_orthonormal_basis]: Federer
    1.10.6, pp. 48-49, the polarity is an isomorphism:
    it carries the monomial basis to the basis of dual one-form products.
    This supporting proof explicitly provides a two-sided linear inverse. *)
Theorem symmetric_polarity_inverse_orthonormal_basis (R : rcfType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e) m :
  exists g : {linear S_m V R^o m -> symmetric_power V m},
    cancel (@inner_symmetric_form R V B hB m) g /\
    cancel g (@inner_symmetric_form R V B hB m).
Proof.
pose omega i := inner_symmetric_polarity hB (e i).
have hd i j : symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) =
    if j == i then 1 else 0.
  by rewrite /omega inner_symmetric_polarityE ho.
have hw := @symmetric_dual_monomial_basis R V n omega e he (@pchar_num R) hd m.
have hg : is_basis (fun a : symmetric_indices n m =>
    inner_symmetric_form hB (symmetric_finite_monomial e a)).
  apply: basis_congr hw=> a; symmetry; exact: symmetric_polarity_monomial.
exact: (@basis_image_inverse_exists R (Choice.clone (symmetric_indices n m) _)
  (symmetric_power V m) (S_m V R^o m) _ (symmetric_finite_monomial_basis he m)
  (@inner_symmetric_form R V B hB m) hg).
Qed.

(** Source for [symmetric_polarity_inverse_exists]: Federer 1.10.6,
    pp. 48-49, the polarity is a linear isomorphism in every
    degree when V is finite dimensional. The supplied finite basis
    need not be orthonormal, and zero dimension and degree are allowed. *)
Theorem symmetric_polarity_inverse_exists (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :
  exists g : {linear S_m V R^o m -> symmetric_power V m},
    cancel (@inner_symmetric_form R V B hB m) g /\
    cancel g (@inner_symmetric_form R V B hB m).
Proof.
have [d [hd ho]] := orthonormal_basis_exists hB he.
exact (@symmetric_polarity_inverse_orthonormal_basis R V B hB n d hd
  (orthonormalisation_orthonormal ho) m).
Qed.
