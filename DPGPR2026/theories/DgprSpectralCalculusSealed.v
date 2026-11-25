(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:spectral: sealed choice of chi^(A). Only the endomorphism and its
    characteristic property are exported; the eigenbasis construction of
    DgprSpectralCalculusConstruction.v is hidden. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import InnerProductUP LinearBasis Hom SymmetricEndomorphisms.
From DPGPR Require Import DgprSpectralCalculusUP DgprSpectralCalculusConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type DgprSpectralCalculusSig.
(** Source for [value]: blueprint def:spectral, the endomorphism
    chi^(A) for chi : R -> R and a symmetric endomorphism A of a space
    with a finite basis. *)
Parameter value : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    (chi : R -> R) (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)),
  Hom V V.
(** Source for [laws]: blueprint def:spectral, the exported map acts by
    chi(a) on each eigenspace ker(A - a 1_V). *)
Parameter laws : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    (chi : R -> R) (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)),
  is_dgpr_spectral_value chi A (@value R V B hB n e he chi A hA).
End DgprSpectralCalculusSig.

Module DgprSpectralCalculus : DgprSpectralCalculusSig.
(** Source for [value]: blueprint def:spectral, choose the proved
    endomorphism inside an opaque module. *)
Definition value (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    (chi : R -> R) (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)) :=
  sval (constructive_indefinite_description (dgpr_spectral_value_exists hB he chi hA)).
(** Source for [laws]: blueprint def:spectral, the selected map has the
    characteristic property. *)
Lemma laws (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    (chi : R -> R) (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)) :
  is_dgpr_spectral_value chi A (@value R V B hB n e he chi A hA).
Proof. exact: (svalP (constructive_indefinite_description (dgpr_spectral_value_exists hB he chi hA))). Qed.
End DgprSpectralCalculus.
