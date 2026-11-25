(** De Philippis, De Rosa and Ghiraldin (2018), (A.3), p. 1143, and DPGPR
    blueprint def:BF: the sealed selection of B_F(T). The value is chosen
    from the characterising predicate [is_ddg_B] of
    DdgAnisotropicIntegrandUP.v; by [ddg_B_unique] it is the only member,
    so the choice is immaterial. This is the only file importing
    DdgAnisotropicIntegrandConstruction.v; downstream files use only the
    interface DdgAnisotropicIntegrand.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations.
From Allard Require Import AllardGrassmann.
From DPDRG Require Import DdgAnisotropicIntegrandUP DdgAnisotropicIntegrandConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type DdgBSignature.
(** Source for [value]: B_F(T) of DDG (A.3), p. 1143, and DPGPR def:BF,
    for an integrand F not depending on the point; 0 when B_F(T) does not
    exist. *)
Parameter value : forall (R : realType) (n d : nat),
  (Hom (R_n R n) (R_n R n) -> R) -> Hom (R_n R n) (R_n R n) -> Hom (R_n R n) (R_n R n).
(** Source for [laws]: the characterising equation of B_F(T), DDG (A.3),
    p. 1143, for T ∈ G(n, d) and F differentiable at T relative to
    G(n, d), Federer 3.1.22, p. 235. *)
Parameter laws : forall (R : realType) (n d : nat) (F : Hom (R_n R n) (R_n R n) -> R)
  (T : Hom (R_n R n) (R_n R n)),
  orthogonal_projectors R n d T -> ddg_relative_differentiable_at d F T ->
  is_ddg_B d F T (@value R n d F T).
End DdgBSignature.

Module DdgB : DdgBSignature.
(** Source for [value]: private selection of the unique solution of the
    characterising equation of DDG (A.3), p. 1143. *)
Definition value (R : realType) (n d : nat) (F : Hom (R_n R n) (R_n R n) -> R)
    (T : Hom (R_n R n) (R_n R n)) : Hom (R_n R n) (R_n R n) :=
  match pselect (exists B, is_ddg_B d F T B) with
  | left h => sval (constructive_indefinite_description h)
  | right _ => 0
  end.
(** Source for [laws]: the selected map satisfies the characterising
    equation of DDG (A.3), p. 1143, by [ddg_B_exists]. *)
Lemma laws (R : realType) (n d : nat) (F : Hom (R_n R n) (R_n R n) -> R)
    (T : Hom (R_n R n) (R_n R n)) :
  orthogonal_projectors R n d T -> ddg_relative_differentiable_at d F T ->
  is_ddg_B d F T (@value R n d F T).
Proof.
move=> hT hF; rewrite /value; case: pselect=> [h|h]; last first.
  by exfalso; apply: h; exact: ddg_B_exists hT hF.
exact: (svalP (constructive_indefinite_description h)).
Qed.
End DdgB.
