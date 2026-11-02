(** Federer (1969), 1.10.5, p. 47, the polarity extension exposed through
    its defining laws. Opaque ascription hides the proved existence
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InnerProductUP InnerSymmetricUP InnerSymmetricConstruction
  AlgebraUP SymmetricAlgebra SymmetricFormUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type InnerSymmetricSig.
(** Source for [map]: Federer 1.10.5, p. 47,
    the abstract unital algebra extension gamma of the polarity. *)
Parameter map : forall (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R), is_inner_product B ->
    algebra_map (symmetric_algebra V) (symmetric_forms_unital_algebra V (scalar_algebra R)).
(** Source for [laws]: Federer 1.10.5, p. 47,
    the required generator and grading laws; the implementation proves them. *)
Parameter laws : forall (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B),
    is_inner_symmetric_extension hB (@map R V B hB).
End InnerSymmetricSig.
Module InnerSymmetric : InnerSymmetricSig.
(** Source for [map]: Federer 1.10.5, p. 47,
    choose the proved witness and hide its implementation. *)
Definition map (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :=
  sval (constructive_indefinite_description (@inner_symmetric_extension_exists R V B hB)).
(** Source for [laws]: Federer 1.10.5, p. 47,
    the selected witness satisfies the defining extension laws. *)
Lemma laws (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  is_inner_symmetric_extension hB (@map R V B hB).
Proof. exact: svalP (constructive_indefinite_description (@inner_symmetric_extension_exists R V B hB)). Qed.
End InnerSymmetric.
