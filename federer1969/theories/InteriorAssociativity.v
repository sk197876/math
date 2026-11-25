(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import ExteriorHomogeneousProducts RightInteriorLaws
  LeftInteriorHom LeftInteriorDegree LeftInterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.1: bounds for the successive left interior products. *)
(** Source for [interior_degree_first]: Federer (1969), 1.5.1, p. 22, last
    paragraph, the two successive-interior-product identities. In words:
    Right interior multiplication reverses the order of successive right
    factors as displayed; left contraction by an alternating product is
    successive left contraction in the displayed order. Supporting lemma for
    this passage; not separately stated in the book. The local LaTeX
    erratum, p. 1, entry for book p. 22 line 9, replaces the letter xi by
    zeta in "for xi in wedge_t V" of the second identity; the degree t is
    printed correctly. *)
Lemma interior_degree_first r s t : (r+s <= t)%N -> (r <= t)%N.
Proof. exact: leq_trans (leq_addr _ _). Qed.
(** Source for [interior_degree_second]: Federer (1969), 1.5.1, p. 22, last
    paragraph, the two successive-interior-product identities. In words:
    Right interior multiplication reverses the order of successive right
    factors as displayed; left contraction by an alternating product is
    successive left contraction in the displayed order. Supporting lemma for
    this passage; not separately stated in the book. The local LaTeX
    erratum, p. 1, entry for book p. 22 line 9, replaces the letter xi by
    zeta in "for xi in wedge_t V" of the second identity; the degree t is
    printed correctly. *)
Lemma interior_degree_second r s t : (r+s <= t)%N -> (s <= t-r)%N.
Proof.
move=> h; rewrite leq_subRL ?(interior_degree_first h) //; exact: h.
Qed.

(** Federer 1.5.1: the form product corresponds to convolution of the
    homogeneous linear maps, as used in the displayed diagram. *)
(** Source for [form_wedge_hom]: Federer (1969), 1.5.1, p. 22, last
    paragraph, the two successive-interior-product identities. In words:
    Right interior multiplication reverses the order of successive right
    factors as displayed; left contraction by an alternating product is
    successive left contraction in the displayed order. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The local LaTeX erratum, p. 1, entry for book p. 22 line 9,
    replaces the letter xi by zeta in "for xi in wedge_t V" of the second
    identity; the degree t is printed correctly. *)
Lemma form_wedge_hom (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) p q (a : A_m V K^o p) (b : A_m V K^o q) :
  (form_homogeneous (form_wedge h2 (scalar_bilinear K) a b) : Hom (exterior_space V) K^o) =
    convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous a) (form_homogeneous b).
Proof. by rewrite /form_wedge homogeneous_formK. Qed.

(** Federer 1.5.1, the second final identity, on actual multivectors.
    exterior_reindex identifies t-(r+s) with (t-r)-s. *)
(** Source for [left_interior_associative]: Federer (1969), 1.5.1, p. 22,
    last paragraph, the two successive-interior-product identities. In
    words: Right interior multiplication reverses the order of successive
    right factors as displayed; left contraction by an alternating product
    is successive left contraction in the displayed order. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. The local LaTeX erratum, p. 1, entry for book p. 22 line 9,
    replaces the letter xi by zeta in "for xi in wedge_t V" of the second
    identity; the degree t is printed correctly. *)
Theorem left_interior_associative (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) r s t (h : (r+s <= t)%N)
  (zeta : exterior_power V t) (a : A_m V K^o r) (b : A_m V K^o s) :
  left_interior h2 h zeta (form_wedge h2 (scalar_bilinear K) a b) =
    exterior_reindex (esym (subnDA r t s))
      (left_interior h2 (interior_degree_second h)
        (left_interior h2 (interior_degree_first h) zeta a) b).
Proof.
apply: val_inj; change
  (component_val (left_interior h2 h zeta (form_wedge h2 (scalar_bilinear K) a b)) =
    component_val (exterior_reindex (esym (subnDA r t s))
      (left_interior h2 (interior_degree_second h)
        (left_interior h2 (interior_degree_first h) zeta a) b))).
rewrite exterior_reindexE !left_interiorE form_wedge_hom.
exact: left_interior_hom_associative.
Qed.
