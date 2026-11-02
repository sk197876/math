(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: evaluation of a one-covector on multiplication by v.
    These identities use the degree-zero summand, in arbitrary dimension. *)
Section Factors.
Variable K : fieldType.
Variable V : lmodType K.
Variable alpha : A_m V K^o 1.
Local Notation E := (exterior_space V).
Local Notation a := (form_homogeneous alpha).
Local Notation ev := (@exterior_generator K V).
(** Source for [one_covector_generator]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma one_covector_generator v : a (ev v) = one_hom alpha v.
Proof.
change (a (exterior_word [tuple v]) = one_hom alpha v).
by rewrite form_homogeneousE form_extensionE form_wordsE one_homE.
Qed.
(** Source for [one_covector_left_factor]: Federer (1969), 1.5.3, p. 23,
    first display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_covector_left_factor v (x : E) :
  a (wedge (ev v) x) = one_hom alpha v * exterior_augmentation V x.
Proof.
elim/exterior_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite (bil0r (wedge_bilinear V)) !linear0 mulr0.
- rewrite (bilDr (wedge_bilinear V)) !linearD.
  change (a (wedge (ev v) x) + a (wedge (ev v) y) =
    one_hom alpha v * (exterior_augmentation V x + exterior_augmentation V y)).
  by rewrite hx hy mulrDr.
- rewrite (bilZr (wedge_bilinear V)) !linearZ.
  change (c * a (wedge (ev v) x) = one_hom alpha v * (c * exterior_augmentation V x)).
  rewrite hx.
  change (c * (one_hom alpha v * exterior_augmentation V x) =
    one_hom alpha v * (c * exterior_augmentation V x)).
  exact: mulrCA.
- case: s => [|w s].
  + by rewrite exterior_word_nil wedge_unitr one_covector_generator exterior_augmentation_unit mulr1.
  + rewrite exterior_augmentation_word /word_degree_zero /= mulr0.
    have hn : (1 + size (w :: s))%N != 1 by rewrite add1n.
    exact: (hom_m_degree a hn (wedge_graded (exterior_generator_homogeneous v)
      (exterior_word_homogeneous (w :: s)))).
Qed.
(** Source for [one_covector_right_factor]: Federer (1969), 1.5.3, p. 23,
    first display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_covector_right_factor v (x : E) :
  a (wedge x (ev v)) = exterior_augmentation V x * one_hom alpha v.
Proof.
elim/exterior_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite (bil0l (wedge_bilinear V)) !linear0 mul0r.
- rewrite (bilDl (wedge_bilinear V)) !linearD.
  change (a (wedge x (ev v)) + a (wedge y (ev v)) =
    (exterior_augmentation V x + exterior_augmentation V y) * one_hom alpha v).
  by rewrite hx hy mulrDl.
- rewrite (bilZl (wedge_bilinear V)) !linearZ.
  change (c * a (wedge x (ev v)) = (c * exterior_augmentation V x) * one_hom alpha v).
  rewrite hx.
  change (c * (exterior_augmentation V x * one_hom alpha v) =
    (c * exterior_augmentation V x) * one_hom alpha v).
  exact: mulrA.
- case: s => [|w s].
  + by rewrite exterior_word_nil wedge_unitl one_covector_generator exterior_augmentation_unit mul1r.
  + rewrite exterior_augmentation_word /word_degree_zero /= mul0r.
    have hn : (size (w :: s) + 1)%N != 1 by rewrite addn1.
    exact: (hom_m_degree a hn (wedge_graded (exterior_word_homogeneous (w :: s))
      (exterior_generator_homogeneous v))).
Qed.
End Factors.
