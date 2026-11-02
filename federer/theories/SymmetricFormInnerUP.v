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

(** Source for [is_symmetric_form_inner_product]: Federer 1.10.6,
    pp. 48-49, opening paragraph. In words: the form-to-Hom
    identification is an isometry for the inner product of 1.7.9.
    This specifies the object independently of its construction. *)
Record is_symmetric_form_inner_product
    (D : S_m V W m -> S_m V W m -> R) : Prop := {
  symmetric_form_inner_laws : is_inner_product D;
  symmetric_form_inner_hom : forall f g,
    D f g = hom_inner (@symmetric_inner_productP R V B hB m) hC
      (finite_ordinal_basis (symmetric_normalized_monomial_basis he m)) (sform_to_hom f) (sform_to_hom g)
}.

(** Source for [symmetric_form_inner_unique]: Federer 1.10.6,
    pp. 48-49, supporting uniqueness: the required isometry
    determines the inner product on forms. *)
Theorem symmetric_form_inner_unique D E :
  is_symmetric_form_inner_product D ->
  is_symmetric_form_inner_product E -> forall f g, D f g = E f g.
Proof.
move=> hD hE f g.
by rewrite (symmetric_form_inner_hom hD) (symmetric_form_inner_hom hE).
Qed.
End Forms.
Arguments is_symmetric_form_inner_product {R V W B C} hB hC {n e} he m D.
