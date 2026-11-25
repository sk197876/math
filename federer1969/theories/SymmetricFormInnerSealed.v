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
From mathcomp.classical Require Import boolp.
From Federer Require Import SymmetricFormInnerUP SymmetricFormInnerConstruction.
Module Type SymmetricFormInnerSig.
(** Source for [product]: Federer 1.10.6, pp. 48-49,
    the inner product on symmetric forms, exposed abstractly. *)
Parameter product : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (m : nat), S_m V W m -> S_m V W m -> R.
(** Source for [laws]: Federer 1.10.6, pp. 48-49,
    the exposed product satisfies its defining isometry and positivity laws. *)
Parameter laws : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (m : nat),
  is_symmetric_form_inner_product hB hC he m (@product R V W B C hB hC n e he m).
End SymmetricFormInnerSig.
Module SymmetricFormInner : SymmetricFormInnerSig.
(** Source for [product]: Federer 1.10.6, pp. 48-49,
    select the proved existence witness inside the sealed module. *)
Definition product (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (m : nat) :=
  sval (constructive_indefinite_description (symmetric_form_inner_exists hB hC he m)).
(** Source for [laws]: Federer 1.10.6, pp. 48-49,
    the selected witness obeys the abstract specification. *)
Lemma laws (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (m : nat) :
  is_symmetric_form_inner_product hB hC he m (@product R V W B C hB hC n e he m).
Proof.
exact: (svalP (constructive_indefinite_description (symmetric_form_inner_exists hB hC he m))).
Qed.
End SymmetricFormInner.
