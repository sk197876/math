(** Federer (1969), 1.10.6, pp. 48-49: the inner product on symmetric
    multilinear forms is transported from Hom by the method of 1.7.9. The
    domain is finite dimensional; the coefficient space need not be. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerSymmetric InnerSymmetricPositivity
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormIsomorphism
  SymmetricNormalizedMonomials LinearBasis FiniteOrdinalBasis HomInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
From Federer Require Import SymmetricFormInnerUP InnerProductPullback.
Section Forms.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.

(** Source for [symmetric_form_inner_exists]: Federer 1.10.6,
    pp. 48-49, existence of the specified inner product by
    pullback through the proved linear isomorphism with Hom.
    The witness is kept behind the sealed interface. *)
Theorem symmetric_form_inner_exists :
  exists D, is_symmetric_form_inner_product hB hC he m D.
Proof.
exists (fun f g => hom_inner (@symmetric_inner_productP R V B hB m) hC
      (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)) (sform_to_hom f) (sform_to_hom g)).
constructor; last by [].
exact (@inner_product_linear_pullback R (S_m V W m) _ _
  (hom_inner_productP (@symmetric_inner_productP R V B hB m) hC
    (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)))
  (@sform_to_hom R V W m) (can_inj (@sform_to_homK R V W m))).
Qed.
End Forms.
