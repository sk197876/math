(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: right exterior multiplication and its induced map
    on Hom. This is the first of the two constructions in the book. *)
Section RightInteriorHom.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation E := (exterior_space V).
(** Source for [right_exterior]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Definition
    or construction used to formalise this passage. *)
Definition right_exterior (eta : E) (xi : E) := wedge xi eta.
(** Source for [right_exterior_linear]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma right_exterior_linear eta : linear (right_exterior eta).
Proof. exact: (proj1 (wedge_bilinear V)). Qed.
HB.instance Definition _ eta := GRing.isLinear.Build K E E *:%R
  (right_exterior eta) (right_exterior_linear eta).
(** Source for [right_interior_hom]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Definition
    or construction used to formalise this passage. *)
Definition right_interior_hom (eta : E) (phi : Hom E W) : Hom E W :=
  hom_comp phi (hom_of_linear (GRing.Linear.clone _ _ _ _ (right_exterior eta) _)).
(** Source for [right_interior_homE]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma right_interior_homE eta phi xi : right_interior_hom eta phi xi = phi (wedge xi eta).
Proof. by []. Qed.
(** Source for [right_interior_hom_bilinear]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma right_interior_hom_bilinear : bilinear right_interior_hom.
Proof.
split.
- move=> phi c eta theta; apply: hom_ext => xi.
  by rewrite !right_interior_homE hom_addE hom_scaleE (proj2 (wedge_bilinear V)) linearP.
- move=> eta c phi psi; apply: hom_ext => xi.
  by rewrite !right_interior_homE !hom_addE !hom_scaleE.
Qed.
(** Federer 1.5.1, first identity in the final paragraph. *)
(** Source for [right_interior_hom_associative]: Federer (1969), 1.5.1, p.
    22, last paragraph, the two successive-interior-product identities. In
    words: Right interior multiplication reverses the order of successive
    right factors as displayed; left contraction by an alternating product
    is successive left contraction in the displayed order. Supporting lemma
    for this passage; not separately stated in the book. The local LaTeX
    erratum, p. 1, entry for book p. 22 line 9, replaces the letter xi by
    zeta in "for xi in wedge_t V" of the second identity; the degree t is
    printed correctly. *)
Theorem right_interior_hom_associative xi eta phi :
  right_interior_hom (wedge xi eta) phi =
    right_interior_hom xi (right_interior_hom eta phi).
Proof. apply: hom_ext => zeta; by rewrite !right_interior_homE wedge_assoc. Qed.
End RightInteriorHom.
