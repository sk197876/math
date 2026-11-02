(** Federer (1969), 1.7.10, p. 35: existence of the endomorphism
    representing a bilinear form in a finite-dimensional inner-product
    space. This private existence proof reuses the polarity argument
    established for 1.7.3. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP LinearBasis
  BilinearRepresentativeUP BilinearRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [bilinear_representative_exists]: Federer 1.7.10,
    p. 35, supporting existence of the uniquely characterised
    endomorphism, with no symmetry assumption on the given form. *)
Theorem bilinear_representative_exists (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) n (e : 'I_n -> V) (he : is_basis e) :
  exists f, is_bilinear_representative B S f.
Proof. exact (@bilinear_endomorphism_representation R V B S hB hS n e he). Qed.
