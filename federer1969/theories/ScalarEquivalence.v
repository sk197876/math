(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors.
From Federer Require Import NonzeroSimple GrassmannSubspaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2: xi and eta are equivalent under the association
    exactly when xi=c eta for some nonzero scalar c. *)
Section Equivalence.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
(** Source for [scalar_equivalent]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition scalar_equivalent (xi eta : nonzero_simple V m) :=
  exists c : K, c != 0 /\ simple_val xi = c *: simple_val eta.
(** Source for [scalar_equivalent_refl]: Federer (1969), 1.6.2, p. 24,
    opening paragraph defining G(V,m). In words: The association from
    nonzero simple m-vectors is onto the set of m-dimensional subspaces; its
    fibres are nonzero scalar proportionality classes. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma scalar_equivalent_refl xi : scalar_equivalent xi xi.
Proof. exists 1; split; [exact: oner_neq0|by rewrite scale1r]. Qed.
(** Source for [scalar_equivalent_sym]: Federer (1969), 1.6.2, p. 24,
    opening paragraph defining G(V,m). In words: The association from
    nonzero simple m-vectors is onto the set of m-dimensional subspaces; its
    fibres are nonzero scalar proportionality classes. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma scalar_equivalent_sym xi eta : scalar_equivalent xi eta -> scalar_equivalent eta xi.
Proof.
move=> [c [hc h]]; exists c^-1; split; first by rewrite invr_eq0.
by rewrite h scalerA mulVf // scale1r.
Qed.
(** Source for [scalar_equivalent_trans]: Federer (1969), 1.6.2, p. 24,
    opening paragraph defining G(V,m). In words: The association from
    nonzero simple m-vectors is onto the set of m-dimensional subspaces; its
    fibres are nonzero scalar proportionality classes. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma scalar_equivalent_trans xi eta zeta :
  scalar_equivalent xi eta -> scalar_equivalent eta zeta -> scalar_equivalent xi zeta.
Proof.
move=> [c [hc h]] [d [hd h']]; exists (c*d); split; first by rewrite mulf_eq0 negb_or hc hd.
by rewrite h h' scalerA.
Qed.
Hypothesis h2 : (1+1 : K) != 0.
(** Source for [associated_G_fibres]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem associated_G_fibres xi eta :
  associated_G h2 xi = associated_G h2 eta <-> scalar_equivalent xi eta.
Proof.
split.
- move=> h; apply: (proj1 (@simple_associated_equal K h2 V m
    (simple_val xi) (simple_val eta) (simple_val_nonzero xi)
    (simple_val_nonzero eta) (simple_val_simple eta))).
  move=> v; have h' := congr1 (fun S => grassmann_val S v) h.
  change (grassmann_val (associated_G h2 xi) v <-> grassmann_val (associated_G h2 eta) v).
  by rewrite h'.
- move=> h; apply: grassmann_ext => v.
  have he := proj2 (@simple_associated_equal K h2 V m
    (simple_val xi) (simple_val eta) (simple_val_nonzero xi)
    (simple_val_nonzero eta) (simple_val_simple eta)) h.
  exact: he v.
Qed.
End Equivalence.
