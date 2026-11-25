(** Federer (1969), 1.7.1, p. 28: choose an orthonormalisation through a
    sealed existence interface. The implementation uses the proved
    Gram-Schmidt witness; downstream results see only orthonormality and
    preservation of prefix spans. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InnerProductUP FiniteIndependence
  OrthonormalisationUP GramSchmidtConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OrthonormalisationSig.
(** Source for [family]: Federer 1.7.1, p. 28,
    the orthonormal sequence whose existence is asserted. *)
Parameter family : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R), is_inner_product B ->
  forall n (u : 'I_n -> V), finite_independent u -> 'I_n -> V.
(** Source for [laws]: Federer 1.7.1, p. 28,
    the asserted orthonormality and equality of every initial span. *)
Parameter laws : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  n (u : 'I_n -> V) (hu : finite_independent u),
  is_orthonormalisation B u (@family R V B hB n u hu).
End OrthonormalisationSig.

Module Orthonormalisation : OrthonormalisationSig.
(** Source for [family]: Federer 1.7.1, p. 28,
    choose the family from the independently proved existence theorem. *)
Definition family (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  n (u : 'I_n -> V) (hu : finite_independent u) : 'I_n -> V :=
  sval (constructive_indefinite_description (@gram_schmidt_witness R V B hB n u hu)).
(** Source for [laws]: Federer 1.7.1, p. 28,
    the chosen existence witness satisfies the abstract specification. *)
Lemma laws (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  n (u : 'I_n -> V) (hu : finite_independent u) :
  is_orthonormalisation B u (@family R V B hB n u hu).
Proof.
exact: svalP (constructive_indefinite_description (@gram_schmidt_witness R V B hB n u hu)).
Qed.
End Orthonormalisation.
