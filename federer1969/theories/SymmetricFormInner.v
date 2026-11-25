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
From Federer Require Import SymmetricFormInnerUP SymmetricFormInnerSealed InnerNorm.
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

(** Source for [symmetric_form_inner]: Federer 1.10.6,
    pp. 48-49, the specified inner product on symmetric forms. *)
Definition symmetric_form_inner := @SymmetricFormInner.product R V W B C hB hC n e he m.

(** Source for [symmetric_form_innerP]: Federer 1.10.6,
    pp. 48-49, the public inner product satisfies the specification. *)
Lemma symmetric_form_innerP :
  is_symmetric_form_inner_product hB hC he m symmetric_form_inner.
Proof. exact: SymmetricFormInner.laws. Qed.

(** Source for [symmetric_form_inner_productP]: Federer 1.10.6,
    pp. 48-49, the resulting bilinear form is an inner product. *)
Theorem symmetric_form_inner_productP : is_inner_product symmetric_form_inner.
Proof. exact: symmetric_form_inner_laws symmetric_form_innerP. Qed.

(** Source for [symmetric_form_innerE]: Federer 1.10.6,
    pp. 48-49, the canonical identification with Hom is an isometry. *)
Theorem symmetric_form_innerE f g : symmetric_form_inner f g =
  hom_inner (@symmetric_inner_productP R V B hB m) hC
      (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)) (sform_to_hom f) (sform_to_hom g).
Proof. exact (@symmetric_form_inner_hom R V W B C hB hC n e he m symmetric_form_inner symmetric_form_innerP f g). Qed.

(** Source for [symmetric_form_norm]: Federer 1.10.6,
    p. 49, the Euclidean length of a symmetric form, distinguished
    from its operator norm in the final displayed inequalities. *)
Definition symmetric_form_norm := inner_norm symmetric_form_inner_productP.

(** Source for [symmetric_form_norm_hom]: Federer 1.10.6,
    pp. 48-49, lengths agree under the canonical Hom identification. *)
Theorem symmetric_form_norm_hom f : symmetric_form_norm f =
  hom_norm (@symmetric_inner_productP R V B hB m) hC
    (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)) (sform_to_hom f).
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr symmetric_form_innerE.
Qed.
End Forms.

Arguments symmetric_form_inner {R V W B C} hB hC {n e} he m _ _.
Arguments symmetric_form_norm {R V W B C} hB hC {n e} he m _.
