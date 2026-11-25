(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra ssrnum generic_quotient.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import SimpleVectors.
From Federer Require Import NonzeroSimple PositiveEquivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

(** Federer 1.6.2: the equivalence classes for positive proportionality
    are oriented m-dimensional subspaces. G_o is the actual quotient set
    of nonzero simple m-vectors under precisely that equivalence. *)
Section Oriented.
Variable R : realFieldType.
Variable V : lmodType R.
Variable m : nat.
(** Source for [oriented_rel]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Definition
    or construction used to formalise this passage. *)
Definition oriented_rel (xi eta : nonzero_simple V m) := `[< positive_equivalent xi eta >].
(** Source for [oriented_rel_refl]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma oriented_rel_refl : reflexive oriented_rel.
Proof. move=> xi; apply/asboolP; exact: positive_equivalent_refl. Qed.
(** Source for [oriented_rel_sym]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma oriented_rel_sym : symmetric oriented_rel.
Proof.
move=> xi eta; apply/idP/idP=> /asboolP h; apply/asboolP;
  exact: positive_equivalent_sym h.
Qed.
(** Source for [oriented_rel_trans]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma oriented_rel_trans : transitive oriented_rel.
Proof.
move=> eta xi zeta /asboolP h /asboolP h'; apply/asboolP.
exact: positive_equivalent_trans h h'.
Qed.
Canonical oriented_equiv := EquivRel oriented_rel oriented_rel_refl oriented_rel_sym oriented_rel_trans.
(** Source for [G_o]: Federer (1969), 1.6.2, p. 24, second paragraph
    defining the finer equivalence and G_o(V,m). In words: Positive scalar
    proportionality defines the oriented m-dimensional subspaces as
    equivalence classes of nonzero simple m-vectors. Definition or
    construction used to formalise this passage. *)
Definition G_o := {eq_quot oriented_rel}.
(** Source for [G_0]: Federer (1969), 1.6.2, p. 24, second paragraph
    defining the finer equivalence and G_o(V,m). In words: Positive scalar
    proportionality defines the oriented m-dimensional subspaces as
    equivalence classes of nonzero simple m-vectors. Definition or
    construction used to formalise this passage. *)
Definition G_0 := G_o.
HB.instance Definition _ := Choice.copy G_o {eq_quot oriented_rel}.
(** Source for [oriented_projection]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Definition
    or construction used to formalise this passage. *)
Definition oriented_projection (xi : nonzero_simple V m) : G_o := \pi_G_o xi.
(** Source for [oriented_projection_eq]: Federer (1969), 1.6.2, p. 24,
    second paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem oriented_projection_eq xi eta :
  oriented_projection xi = oriented_projection eta <-> positive_equivalent xi eta.
Proof.
split=> h.
- apply/asboolP; apply/(eqmodP oriented_equiv); exact: h.
- apply/(eqmodP oriented_equiv)/asboolP; exact: h.
Qed.
(** Source for [oriented_projection_surjective]: Federer (1969), 1.6.2, p.
    24, second paragraph defining the finer equivalence and G_o(V,m). In
    words: Positive scalar proportionality defines the oriented
    m-dimensional subspaces as equivalence classes of nonzero simple
    m-vectors. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem oriented_projection_surjective : forall q : G_o, exists xi, oriented_projection xi = q.
Proof. move=> q; exists (repr q); exact: reprK. Qed.
End Oriented.
Arguments G_o {R} V m.
Arguments G_0 {R} V m.
