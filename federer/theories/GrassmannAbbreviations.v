(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra ssrnum.
From Federer Require Import SimpleVectors.
From Federer Require Import GrassmannSubspaces OrientedGrassmann.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.6.2, final display: the abbreviations G(n,m)=G(R^n,m)
    and G_o(n,m)=G_o(R^n,m). The two overloaded book names are retained
    in a separate namespace. R_n is the ordinary space of real-valued
    functions on the n coordinate indices. *)
(** Source for [R_n]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Definition or construction used to formalise this
    passage. this project follows Federer. *)
Definition R_n (R : realFieldType) n : lmodType R :=
  GRing.Lmodule.clone R {ffun 'I_n -> R^o} _.
Module FedererEuclideanGrassmann.
Section Abbreviations.
Variable R : realFieldType.
(** Source for [G]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Definition or construction used to formalise this
    passage. this project follows Federer. *)
Definition G n m := GrassmannSubspaces.G (R_n R n) m.
(** Source for [G_o]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Definition or construction used to formalise this
    passage. this project follows Federer. *)
Definition G_o n m := OrientedGrassmann.G_o (R_n R n) m.
(** Source for [G_0]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Definition or construction used to formalise this
    passage. this project follows Federer. *)
Definition G_0 n m := OrientedGrassmann.G_0 (R_n R n) m.
(** Source for [GE]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Supporting lemma for this passage; not separately
    stated in the book. this project follows Federer. *)
Lemma GE n m : G n m = GrassmannSubspaces.G (R_n R n) m.
Proof. by []. Qed.
(** Source for [G_oE]: Federer (1969), 1.6.2, p. 24, last display. In words:
    For Euclidean ambient space R^n, abbreviate G(R^n,m) and G_o(R^n,m) by
    G(n,m) and G_o(n,m). Supporting lemma for this passage; not separately
    stated in the book. this project follows Federer. *)
Lemma G_oE n m : G_o n m = OrientedGrassmann.G_o (R_n R n) m.
Proof. by []. Qed.
End Abbreviations.
End FedererEuclideanGrassmann.
