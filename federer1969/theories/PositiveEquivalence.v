(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra ssrnum.
From Federer Require Import SimpleVectors.
From Federer Require Import NonzeroSimple ScalarEquivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2: the finer equivalence relation uses a positive
    real scalar. Reflexivity, symmetry and transitivity are proved. *)
Section Positive.
Variable R : realFieldType.
Variable V : lmodType R.
Variable m : nat.
(** Source for [positive_equivalent]: Federer (1969), 1.6.2, p. 24, second
    paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Definition
    or construction used to formalise this passage. *)
Definition positive_equivalent (xi eta : nonzero_simple V m) :=
  exists c : R, 0<c /\ simple_val xi = c *: simple_val eta.
(** Source for [positive_equivalent_refl]: Federer (1969), 1.6.2, p. 24,
    second paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma positive_equivalent_refl xi : positive_equivalent xi xi.
Proof. exists 1; split; [exact: ltr01|by rewrite scale1r]. Qed.
(** Source for [positive_equivalent_sym]: Federer (1969), 1.6.2, p. 24,
    second paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma positive_equivalent_sym xi eta : positive_equivalent xi eta -> positive_equivalent eta xi.
Proof.
move=> [c [hc h]]; exists c^-1; split; first by rewrite invr_gt0.
have hc0 : c != 0 := lt0r_neq0 hc.
by rewrite h scalerA mulVf // scale1r.
Qed.
(** Source for [positive_equivalent_trans]: Federer (1969), 1.6.2, p. 24,
    second paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma positive_equivalent_trans xi eta zeta :
  positive_equivalent xi eta -> positive_equivalent eta zeta -> positive_equivalent xi zeta.
Proof.
move=> [c [hc h]] [d [hd h']]; exists (c*d); split; first exact: mulr_gt0.
by rewrite h h' scalerA.
Qed.
(** Source for [positive_equivalence_finer]: Federer (1969), 1.6.2, p. 24,
    second paragraph defining the finer equivalence and G_o(V,m). In words:
    Positive scalar proportionality defines the oriented m-dimensional
    subspaces as equivalence classes of nonzero simple m-vectors. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem positive_equivalence_finer xi eta :
  positive_equivalent xi eta -> scalar_equivalent xi eta.
Proof. move=> [c [hc h]]; exists c; split=> //; exact: lt0r_neq0. Qed.
End Positive.
