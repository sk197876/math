(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2: the domain of the association is the set of all
    nonzero simple m-vectors, with exactly the definition of 1.6.1. *)
Section Domain.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
(** Source for [nonzero_simple_pred]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition nonzero_simple_pred (xi : exterior_power V m) :=
  (xi != 0) && `[< simple xi >].
(** Source for [nonzero_simple]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Record nonzero_simple := NonzeroSimple {
  simple_val : exterior_power V m;
  simple_proof : nonzero_simple_pred simple_val
}.
(** Source for [simple_rect]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition simple_rect (P : nonzero_simple -> Type)
  (h : forall xi hx, P (@NonzeroSimple xi hx)) (z : nonzero_simple) : P z :=
  match z as z' return P z' with @NonzeroSimple xi hx => h xi hx end.
HB.instance Definition _ := [isSub for simple_val by simple_rect].
HB.instance Definition _ := [Choice of nonzero_simple by <:].
(** Source for [simple_val_nonzero]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma simple_val_nonzero (xi : nonzero_simple) : simple_val xi != 0.
Proof. exact: (proj1 (elimT andP (simple_proof xi))). Qed.
(** Source for [simple_val_simple]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma simple_val_simple (xi : nonzero_simple) : simple (simple_val xi).
Proof. apply/asboolP; exact: (proj2 (elimT andP (simple_proof xi))). Qed.
(** Source for [nonzero_simple_lift]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition nonzero_simple_lift xi (hx : xi != 0) (hs : simple xi) : nonzero_simple :=
  @NonzeroSimple xi (introT andP (conj hx (introT (asboolP _) hs))).
(** Source for [nonzero_simple_liftE]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma nonzero_simple_liftE xi hx hs : simple_val (@nonzero_simple_lift xi hx hs) = xi.
Proof. by []. Qed.
End Domain.
Arguments nonzero_simple {K} V m.
Arguments simple_val {K V m} _.
