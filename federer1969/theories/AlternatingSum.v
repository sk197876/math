(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Exterior.
From Federer Require Import Hom HomogeneousHom AlternatingForms AlternatingWords
  AlternatingExtension AlternatingIsomorphism BoundedHom HomogeneousSum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1: A^*(V,W) is the direct sum of the A^m(V,W).
    We realise it in the linearly isomorphic homogeneous-map model from
    the preceding paragraph, and prove the component identifications,
    their inverse law, orthogonality, and finite reconstruction. *)
Section AlternatingSum.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [A_star]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition A_star := Hom_finite W (exterior_grading V).
(** Source for [A_star_grading]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition A_star_grading : grading A_star := hom_finite_grading W (exterior_grading V).
(** Source for [form_include]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition form_include m (f : A_m V W m) : A_star := homogeneous_include (form_homogeneous f).
(** Source for [form_component]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition form_component m (f : A_star) : A_m V W m := homogeneous_form (homogeneous_piece m f).
(** Source for [form_includeE]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_includeE m (f : A_m V W m) x : form_include f x = form_extension f x.
Proof. by []. Qed.
(** Source for [form_componentE]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_componentE m f (t : m.-tuple V) : form_component m f t = f (exterior_word t).
Proof.
rewrite /form_component homogeneous_formE homogeneous_pieceE.
change (f (exterior_degree m (exterior_word t)) = f (exterior_word t)).
by rewrite exterior_degree_word size_tuple eqxx.
Qed.
(** Source for [form_include_linear]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma form_include_linear m : linear (@form_include m).
Proof. move=> a f g; by rewrite /form_include !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (A_m V W m) A_star
  *:%R (@form_include m) (@form_include_linear m).
(** Source for [form_component_linear]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma form_component_linear m : linear (form_component m).
Proof. move=> a f g; by rewrite /form_component !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K A_star (A_m V W m)
  *:%R (form_component m) (form_component_linear m).
(** Source for [form_includeK]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma form_includeK m : cancel (@form_include m) (form_component m).
Proof. move=> f; by rewrite /form_include /form_component homogeneous_includeK form_homogeneousK. Qed.
(** Source for [form_componentK]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma form_componentK m f : form_include (form_component m f) = grade A_star_grading m f.
Proof.
by rewrite /form_include /form_component homogeneous_formK homogeneous_pieceK.
Qed.
(** Source for [form_include_grade]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma form_include_grade n m (f : A_m V W m) :
  grade A_star_grading n (form_include f) = if n == m then form_include f else 0.
Proof. exact: homogeneous_include_grade. Qed.
(** Source for [form_include_homogeneous]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma form_include_homogeneous m (f : A_m V W m) :
  homogeneous A_star_grading m (form_include f).
Proof. by rewrite /homogeneous form_include_grade eqxx. Qed.
(** Source for [alternating_sum_decomposition]: Federer (1969), 1.4.1, p.
    17, definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem alternating_sum_decomposition f : exists N,
  f = \sum_(i < N) form_include (form_component i f).
Proof.
have [N hN] := grade_finite A_star_grading f; exists N.
by under eq_bigr do rewrite form_componentK.
Qed.
(** Source for [alternating_sum_ext]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alternating_sum_ext (f g : A_star) :
  (forall m, form_component m f = form_component m g) -> f = g.
Proof.
move=> h; apply: hom_finite_ext => x.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite !linearZ; exact (congr1 (fun y : W => a *: y) hx).
- have he := congr1 (fun a : A_m V W (size s) => a (in_tuple s)) (h (size s)).
  by rewrite !form_componentE in he.
Qed.
(** Source for [alternating_sum_induction]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma alternating_sum_induction (P : A_star -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
  (hF : forall m (f : A_m V W m), P (form_include f)) : forall f, P f.
Proof.
move=> f; have [N ->] := alternating_sum_decomposition f.
apply: big_ind => // i _; exact: hF.
Qed.
End AlternatingSum.
Arguments A_star {K} V W.

(** Federer 1.4.1: A^m V and A^* V abbreviate the scalar-valued spaces.
    In particular an m-covector is an element of A^m V. *)
(** Source for [covector]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition covector (K : fieldType) (V : lmodType K) m := A_m V K^o m.
(** Source for [A_covectors]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition A_covectors (K : fieldType) (V : lmodType K) := A_star V K^o.
Arguments covector {K} V m.
Arguments A_covectors {K} V.
