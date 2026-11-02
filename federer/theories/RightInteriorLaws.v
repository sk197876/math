(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import ExteriorHomogeneousProducts RightInteriorHom RightInterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: the actual right exterior map between the stated
    homogeneous components and its induced map on Hom. *)
Section Induced.
Variable K : fieldType.
Variables V W : lmodType K.
Variables p q : nat.
Variable hpq : (p <= q)%N.
(** Source for [right_exterior_power]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Definition
    or construction used to formalise this passage. *)
Definition right_exterior_power (eta : exterior_power V p) (xi : exterior_power V (q-p)) : exterior_power V q :=
  exterior_reindex (subnK hpq) (exterior_product xi eta).
(** Source for [right_exterior_powerE]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma right_exterior_powerE eta xi : component_val (right_exterior_power eta xi) =
  wedge (component_val xi) (component_val eta).
Proof. by rewrite /right_exterior_power exterior_reindexE exterior_productE. Qed.
(** Source for [right_exterior_power_linear]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma right_exterior_power_linear eta : linear (right_exterior_power eta).
Proof.
move=> a xi zeta; rewrite /right_exterior_power
  (proj1 (exterior_product_bilinear V (q-p) p)) linearP; by [].
Qed.
HB.instance Definition _ eta := GRing.isLinear.Build K (exterior_power V (q-p)) (exterior_power V q)
  *:%R (right_exterior_power eta) (right_exterior_power_linear eta).
(** Source for [right_interior_pairing]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_pairing eta (phi : A_m V W q) xi :
  pairing xi (right_interior hpq eta phi) = pairing (right_exterior_power eta xi) phi.
Proof.
rewrite right_interior_characteristic.
change (form_homogeneous phi (wedge (component_val xi) (component_val eta)) =
  form_homogeneous phi (component_val (right_exterior_power eta xi))).
by rewrite right_exterior_powerE.
Qed.
(** Source for [right_interior_induced]: Federer (1969), 1.5.1, p. 21,
    right-exterior-multiplication construction. In words: Precomposition
    with right exterior multiplication gives the operation on linear maps
    and, via the form identification, the right interior product. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem right_interior_induced eta (phi : A_m V W q) :
  form_to_hom (right_interior hpq eta phi) =
    hom_comp (form_to_hom phi)
      (hom_of_linear (GRing.Linear.clone _ _ _ _ (right_exterior_power eta) _)).
Proof. apply: hom_ext => xi; exact: right_interior_pairing. Qed.
End Induced.

(** Federer 1.5.1, r+s <= t supplies the two bounds required to
    perform successive interior multiplications. *)
(** Source for [interior_degree_s]: Federer (1969), 1.5.1, p. 22, last
    paragraph, the two successive-interior-product identities. In words:
    Right interior multiplication reverses the order of successive right
    factors as displayed; left contraction by an alternating product is
    successive left contraction in the displayed order. Supporting lemma for
    this passage; not separately stated in the book. The local LaTeX
    erratum, p. 1, entry for book p. 22 line 9, replaces the letter xi by
    zeta in "for xi in wedge_t V" of the second identity; the degree t is
    printed correctly. *)
Lemma interior_degree_s r s t : (r+s <= t)%N -> (s <= t)%N.
Proof. exact: leq_trans (leq_addl _ _). Qed.
(** Source for [interior_degree_r]: Federer (1969), 1.5.1, p. 22, last
    paragraph, the two successive-interior-product identities. In words:
    Right interior multiplication reverses the order of successive right
    factors as displayed; left contraction by an alternating product is
    successive left contraction in the displayed order. Supporting lemma for
    this passage; not separately stated in the book. The local LaTeX
    erratum, p. 1, entry for book p. 22 line 9, replaces the letter xi by
    zeta in "for xi in wedge_t V" of the second identity; the degree t is
    printed correctly. *)
Lemma interior_degree_r r s t : (r+s <= t)%N -> (r <= t-s)%N.
Proof.
move=> h; rewrite leq_subRL ?(interior_degree_s h) // addnC; exact: h.
Qed.

(** Federer 1.5.1, first final identity, on the actual forms.
    form_reindex merely identifies t-(r+s) with (t-s)-r. *)
(** Source for [right_interior_associative]: Federer (1969), 1.5.1, p. 22,
    last paragraph, the two successive-interior-product identities. In
    words: Right interior multiplication reverses the order of successive
    right factors as displayed; left contraction by an alternating product
    is successive left contraction in the displayed order. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The local LaTeX erratum, p. 1, entry for book p. 22 line 9,
    replaces the letter xi by zeta in "for xi in wedge_t V" of the second
    identity; the degree t is printed correctly. *)
Theorem right_interior_associative (K : fieldType) (V W : lmodType K)
  r s t (h : (r+s <= t)%N) (xi : exterior_power V r)
  (eta : exterior_power V s) (phi : A_m V W t) :
  right_interior h (exterior_product xi eta) phi =
    form_reindex (esym (subnDAC t r s))
      (right_interior (interior_degree_r h) xi
        (right_interior (interior_degree_s h) eta phi)).
Proof.
apply: (can_inj (@form_homogeneousK K V W (t-(r+s)))).
apply: hom_m_ext => zeta.
by rewrite form_reindexE !right_interior_homogeneousE exterior_productE wedge_assoc.
Qed.
