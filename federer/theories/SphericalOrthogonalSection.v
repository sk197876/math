(** Federer (1969), 3.2.47, p. 282: public exact
    local section F. Downstream proofs use only its independent
    domain and normalized basis-value laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations LinearBasis PartialFunctionUP
  SphericalOrthogonalSectionUP SphericalOrthogonalSectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_section]: the actual normalized
    local section F in 3.2.47, p. 282, exposed through
    an opaque independent specification. *)
Definition spherical_orthogonal_section (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e):=
  @SphericalOrthogonalSection.value R n e he.

(** Source for [spherical_orthogonal_section_laws]: exact public
    laws for F in 3.2.47, p. 282. Regularity and
    geometric identities are separate conclusions. *)
Lemma spherical_orthogonal_section_laws (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e):
  is_spherical_orthogonal_section_graph e (spherical_orthogonal_section he).
Proof. exact:SphericalOrthogonalSection.laws. Qed.

(** Source for [spherical_orthogonal_section_domain]: the section's
    exact printed U in 3.2.47, p. 282, with both
    possible signs of the first coordinate. *)
Lemma spherical_orthogonal_section_domain (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e):
  partial_function_domain (spherical_orthogonal_section he)=spherical_frame_patch e.
Proof. exact:spherical_section_domain (spherical_orthogonal_section_laws he). Qed.

(** Source for [spherical_orthogonal_section_graph]: the exact
    positive recurrence determines each original section value,
    as in 3.2.47, p. 282. *)
Lemma spherical_orthogonal_section_graph (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e) u F:
  partial_function_graph (spherical_orthogonal_section he) u F<->
    has_spherical_orthogonal_section e u F.
Proof. exact (@spherical_section_value R n e (spherical_orthogonal_section he)
  (spherical_orthogonal_section_laws he) u F). Qed.
