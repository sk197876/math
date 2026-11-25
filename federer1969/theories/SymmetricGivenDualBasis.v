(** Federer (1969), 1.10.6, p. 49: the normalized covector assertions hold
    for the supplied dual basis omega, not merely for a separately chosen
    family. The lemma below identifies a given dual basis with the polarity
    of the orthonormal primal basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import Hom TensorUP LinearBasis InnerProductUP OrthonormalFamilies
  InnerSymmetricPolarity SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricForms SymmetricFormIsomorphism SymmetricPairing SymmetricNormalizedDualMonomials
  SymmetricFormInner ScalarInnerProduct SymmetricMultiIndices SymmetricIndexBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section GivenDual.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable omega : 'I_n -> S_m V R^o 1.
Hypothesis hd : forall i j,
  symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) =
    if j == i then 1 else 0.

(** Source for [symmetric_given_dual_is_polarity]: Federer 1.10.6,
    p. 49, supporting uniqueness: the given dual one-form omega_i
    is the polarity of e_i when the primal basis is orthonormal. *)
Lemma symmetric_given_dual_is_polarity i : omega i = inner_symmetric_polarity hB (e i).
Proof.
have hh x : symmetric_pairing (symmetric_first_inclusion V x) (omega i) =
    symmetric_pairing (symmetric_first_inclusion V x) (inner_symmetric_polarity hB (e i)).
  apply: (basis_linear_ext he
    (linear_comp (hom_as_linear (sform_to_hom (omega i))) (symmetric_first_inclusion V))
    (linear_comp (hom_as_linear (sform_to_hom (inner_symmetric_polarity hB (e i))))
      (symmetric_first_inclusion V))) x=> j.
  change (symmetric_pairing (symmetric_first_inclusion V (e j)) (omega i) =
    symmetric_pairing (symmetric_first_inclusion V (e j)) (inner_symmetric_polarity hB (e i))).
  by rewrite hd inner_symmetric_polarityE ho.
apply: symmetric_pairing_ext=> x.
rewrite -{1}(symmetric_first_inverseK x) hh symmetric_first_inverseK.
by [].
Qed.

(** Source for [symmetric_given_dual_normalized_basis]: Federer 1.10.6,
    p. 49, the normalized products of the given dual basis
    form a basis in each degree. *)
Theorem symmetric_given_dual_normalized_basis m :
  is_basis (@symmetric_normalized_dual_monomial R V n omega m).
Proof.
have hw : omega = (fun i => inner_symmetric_polarity hB (e i)).
  exact: funext symmetric_given_dual_is_polarity.
rewrite hw; exact: (@symmetric_normalized_dual_basis R V B hB n e he ho m).
Qed.

(** Source for [symmetric_given_dual_normalized_orthonormal]: Federer
    1.10.6, p. 49, the normalized products of the given
    dual basis are orthonormal for the specified scalar form metric. *)
Theorem symmetric_given_dual_normalized_orthonormal m :
  orthonormal_family (symmetric_form_inner hB (scalar_inner_productP R) he m)
    (@symmetric_normalized_dual_monomial R V n omega m).
Proof.
have hw : omega = (fun i => inner_symmetric_polarity hB (e i)).
  exact: funext symmetric_given_dual_is_polarity.
rewrite hw; exact: (@symmetric_normalized_dual_orthonormal R V B hB n e he ho m).
Qed.
End GivenDual.
