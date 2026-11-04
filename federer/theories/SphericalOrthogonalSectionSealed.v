(** Federer (1969), 3.2.47, p. 282: opaque local
    section with the exact printed domain and recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations LinearBasis PartialFunctionUP
  SphericalOrthogonalSectionUP SphericalOrthogonalSectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SphericalOrthogonalSectionSignature.
(** Source for [value]: the exact normalized section F in
    3.2.47, p. 282, with no chosen extension outside U. *)
Parameter value:forall (R:realType) n (e:'I_n.+1->R_n R n.+1),
  is_basis e->partial_function (R_n R n.+1) (Hom (R_n R n.+1) (R_n R n.+1)).
(** Source for [laws]: the exact-domain and recurrence laws
    of F in 3.2.47, p. 282, independently of construction. *)
Parameter laws:forall (R:realType) n (e:'I_n.+1->R_n R n.+1) (he:is_basis e),
  is_spherical_orthogonal_section_graph e (@value R n e he).
End SphericalOrthogonalSectionSignature.

Module SphericalOrthogonalSection:SphericalOrthogonalSectionSignature.
(** Source for [value]: opaque selection from the proved section
    existence in 3.2.47, p. 282. *)
Definition value (R:realType) n (e:'I_n.+1->R_n R n.+1) (he:is_basis e):=
  projT1 (cid (@spherical_orthogonal_section_graph_exists R n e he)).
(** Source for [laws]: the selected section satisfies its
    independent laws, 3.2.47, p. 282. *)
Lemma laws (R:realType) n (e:'I_n.+1->R_n R n.+1) (he:is_basis e):
  is_spherical_orthogonal_section_graph e (@value R n e he).
Proof. exact:projT2 (cid (@spherical_orthogonal_section_graph_exists R n e he)). Qed.
End SphericalOrthogonalSection.
