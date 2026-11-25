(** Federer (1969), 3.4.8(8), p. 329:
    the proved extension to fractions has an opaque
    map governed by its original coefficient equation.
    The choice of numerators remains private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import FractionFieldUP FractionFieldExtensionUP FractionFieldExtensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FractionFieldExtensionSignature.
(** Source for [map]: the original coefficient
    embedding extended to fractions, supporting
    M inside L in 3.4.8(8), p. 329. *)
Parameter map:forall (A:comNzRingType) (L K:fieldType) (embed:{rmorphism A->L}),
  is_commutative_fraction_field embed ->forall f:{rmorphism A->K},
    injective f ->{rmorphism L->K}.
(** Source for [laws]: the extension retains every
    original coefficient, 3.4.8(8), p. 329. *)
Parameter laws:forall (A:comNzRingType) (L K:fieldType) (embed:{rmorphism A->L})
  (hField:is_commutative_fraction_field embed) (f:{rmorphism A->K}) (hFaithful:injective f),
    is_fraction_field_extension embed f (@map A L K embed hField f hFaithful).
End FractionFieldExtensionSignature.
Module FractionFieldExtension:FractionFieldExtensionSignature.
(** Source for [map]: a hidden witness of the
    proved extension theorem, supporting M in
    3.4.8(8), p. 329. *)
Definition map (A:comNzRingType) (L K:fieldType) (embed:{rmorphism A->L})
  (hField:is_commutative_fraction_field embed) (f:{rmorphism A->K}) (hFaithful:injective f):
  {rmorphism L->K}:=
  projT1 (cid (@fraction_field_extension_exists A L K embed hField f hFaithful)).
(** Source for [laws]: the selected map satisfies
    the independent extension equation,
    3.4.8(8), p. 329. *)
Lemma laws (A:comNzRingType) (L K:fieldType) (embed:{rmorphism A->L})
  (hField:is_commutative_fraction_field embed) (f:{rmorphism A->K}) (hFaithful:injective f):
    is_fraction_field_extension embed f (@map A L K embed hField f hFaithful).
Proof. exact:(projT2 (cid (@fraction_field_extension_exists A L K embed hField f hFaithful))). Qed.
End FractionFieldExtension.
