(** Federer (1969), 1.7.10, p. 35: sealed associated endomorphism for a
    bilinear form. Only the endomorphism and its characterising equation are
    exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP TensorUP LinearBasis
  BilinearRepresentativeUP BilinearRepresentativeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type BilinearRepresentativeSig.
(** Source for [map]: Federer 1.7.10, p. 35,
    the associated endomorphism of a finite-dimensional inner-product space. *)
Parameter map : forall (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (e : 'I_n -> V) (he : is_basis e),
  {linear V -> V}.
(** Source for [laws]: Federer 1.7.10, p. 35,
    the exported endomorphism satisfies the characterising equation. *)
Parameter laws : forall (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (e : 'I_n -> V) (he : is_basis e),
  is_bilinear_representative B S (@map R V B S hB hS n e he).
End BilinearRepresentativeSig.
Module BilinearRepresentative : BilinearRepresentativeSig.
(** Source for [map]: Federer 1.7.10, p. 35,
    select the proved existence witness inside the opaque module. *)
Definition map (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (e : 'I_n -> V) (he : is_basis e) :=
  sval (constructive_indefinite_description (bilinear_representative_exists hB hS he)).
(** Source for [laws]: Federer 1.7.10, p. 35,
    the selected witness satisfies the abstract specification. *)
Lemma laws (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (e : 'I_n -> V) (he : is_basis e) :
  is_bilinear_representative B S (@map R V B S hB hS n e he).
Proof. exact: (svalP (constructive_indefinite_description (bilinear_representative_exists hB hS he))). Qed.
End BilinearRepresentative.
