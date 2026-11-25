(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import InteriorComplements InteriorIndexRelations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.5.2: mu is now the identity index of all n basis vectors. *)
(** Source for [Lambda_top_set]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma Lambda_top_set n : Lambda_set (Lambda_top n) = setT.
Proof.
apply/setP=> i; rewrite /Lambda_set /Lambda_top !inE /=.
by rewrite mem_enum.
Qed.
(** Source for [Lambda_subset_top]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma Lambda_subset_top n p (lambda : Lambda n p) :
  Lambda_set lambda \subset Lambda_set (Lambda_top n).
Proof. by rewrite Lambda_top_set subsetT. Qed.
(** Source for [top_complement]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Definition or construction used to formalise this passage. *)
Definition top_complement n p (lambda : Lambda n p) : Lambda n (n-p) := nu (Lambda_subset_top lambda).
(** Source for [top_complement_disjoint]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma top_complement_disjoint n p (lambda : Lambda n p) :
  uniq (val lambda ++ val (top_complement lambda)).
Proof. exact: nu_disjoint. Qed.
(** Source for [top_complement_permutation]: Federer (1969), 1.5.2, p. 22,
    last paragraph, top-degree products and D_p and D^p. In words:
    Contraction with dual top-degree basis elements gives the two duality
    isomorphisms; D_p and D^(n-p) are inverse, and depend only on those
    top-degree elements. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma top_complement_permutation n p (lambda : Lambda n p) :
  perm_eq (val lambda ++ val (top_complement lambda)) (val (Lambda_top n)).
Proof. exact: nu_permutation. Qed.
(** Source for [top_complement_shared_right]: Federer (1969), 1.5.2, p. 22,
    last paragraph, top-degree products and D_p and D^p. In words:
    Contraction with dual top-degree basis elements gives the two duality
    isomorphisms; D_p and D^(n-p) are inverse, and depend only on those
    top-degree elements. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma top_complement_shared_right n p (lambda mu : Lambda n p) :
  perm_eq (val mu ++ val (top_complement lambda)) (val (Lambda_top n)) = (mu == lambda).
Proof.
apply/idP/idP.
- move=> h; apply/eqP; apply: Lambda_perm_equal.
  have hback : perm_eq (val (Lambda_top n)) (val lambda ++ val (top_complement lambda)).
    by rewrite perm_sym; exact: top_complement_permutation.
  have he := perm_trans h hback; by rewrite perm_cat2r in he.
- move/eqP=> ->; exact: top_complement_permutation.
Qed.
(** Source for [top_complement_shared_left]: Federer (1969), 1.5.2, p. 22,
    last paragraph, top-degree products and D_p and D^p. In words:
    Contraction with dual top-degree basis elements gives the two duality
    isomorphisms; D_p and D^(n-p) are inverse, and depend only on those
    top-degree elements. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma top_complement_shared_left n p (lambda mu : Lambda n p) :
  perm_eq (val (top_complement lambda) ++ val mu) (val (Lambda_top n)) = (mu == lambda).
Proof. by rewrite perm_catC top_complement_shared_right. Qed.
