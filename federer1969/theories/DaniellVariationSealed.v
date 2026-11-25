(** Opaque positive-variation implementation for Federer (1969), 2.5.5, p.
    96 Only the functional and its supremum specification are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP DaniellVariationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DaniellVariationSignature.
  (** Source for [value]: mu+ from Federer 2.5.5, p. 96 *)
  Parameter value : forall (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R),
    is_function_lattice L -> is_daniell_integral L A -> (X -> R) -> R.
  (** Source for [laws]: supremum equation for mu+ in Federer 2.5.5, p. 96 *)
  Parameter laws : forall (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A),
    is_daniell_positive_variation L A (@value R X L A hL hA).
End DaniellVariationSignature.
Module DaniellVariation : DaniellVariationSignature.
(** Source for [value]: witness of the positive variation in Federer 2.5.5,
    p. 96 *)
Definition value (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :=
  projT1 (cid (@daniell_positive_variation_exists R X L A hL hA)).
(** Source for [laws]: proved supremum specification of the witness in
    Federer 2.5.5, p. 96 No new global assumption is introduced. *)
Lemma laws (R : realType) (X : Type) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A) :
  is_daniell_positive_variation L A (@value R X L A hL hA).
Proof. exact: (projT2 (cid (@daniell_positive_variation_exists R X L A hL hA))). Qed.
End DaniellVariation.
