(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import GradedAlgebra GradedSums.
From Federer Require Import Hom HomogeneousHom BoundedHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, direct-sum inclusions and projections. These equations
    identify Hom_finite with the direct sum of the spaces Hom^m. *)
Section HomogeneousSum.
Variable K : fieldType.
Variables V W : lmodType K.
Variable G : grading V.
Local Notation S := (Hom_finite W G).

(** Source for [hom_m_bounded]: Federer (1969), 1.4.1, p. 17, definition of
    A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_m_bounded m (f : Hom_m W G m) : hom_bounded G f m.+1.
Proof.
move=> n x hn hx; apply: hom_m_degree hx.
by rewrite neq_ltn hn orbT.
Qed.
(** Source for [homogeneous_include]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Definition or construction used to formalise this passage. *)
Definition homogeneous_include m (f : Hom_m W G m) : S :=
  @FiniteHom K V W G f
    (introT (asboolP _) (ex_intro _ m.+1 (hom_m_bounded f))).
(** Source for [homogeneous_includeE]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_includeE m (f : Hom_m W G m) x : homogeneous_include f x = f x.
Proof. by []. Qed.
(** Source for [homogeneous_include_linear]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_include_linear m : linear (@homogeneous_include m).
Proof. move=> a f g; apply: hom_finite_ext => x; by []. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (Hom_m W G m) S
  *:%R (@homogeneous_include m) (@homogeneous_include_linear m).

(** Source for [homogeneous_piece]: Federer (1969), 1.4.1, p. 17, definition
    of A^*(V,W) and scalar abbreviations. In words: The full space of
    alternating forms is the direct sum of the spaces of forms of each
    degree; scalar-valued degree-m forms are called m-covectors. Definition
    or construction used to formalise this passage. *)
Definition homogeneous_piece m (f : S) : Hom_m W G m :=
  @HomogeneousHom K V W G m (hom_projection G m f)
    (introT (asboolP _) (@hom_projection_degree K V W G m f)).
(** Source for [homogeneous_pieceE]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_pieceE m f x : homogeneous_piece m f x = f (grade G m x).
Proof. by []. Qed.
(** Source for [homogeneous_piece_linear]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_piece_linear m : linear (homogeneous_piece m).
Proof.
move=> a f g; apply: hom_m_ext => x.
by rewrite homogeneous_pieceE hom_finite_addE hom_finite_scaleE hom_m_addE hom_m_scaleE.
Qed.
HB.instance Definition _ m := GRing.isLinear.Build K S (Hom_m W G m)
  *:%R (homogeneous_piece m) (homogeneous_piece_linear m).

(** Source for [homogeneous_includeK]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_includeK m : cancel (@homogeneous_include m) (homogeneous_piece m).
Proof.
move=> f; apply: hom_m_ext => x.
rewrite homogeneous_pieceE homogeneous_includeE; exact: hom_m_projection.
Qed.
(** Source for [homogeneous_pieceK]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_pieceK m f : homogeneous_include (homogeneous_piece m f) = finite_hom_grade m f.
Proof. apply: hom_finite_ext => x; by []. Qed.
(** Source for [homogeneous_include_grade]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_include_grade n m (f : Hom_m W G m) :
  finite_hom_grade n (homogeneous_include f) = if n == m then homogeneous_include f else 0.
Proof.
apply: hom_finite_ext => x; rewrite finite_hom_gradeE homogeneous_includeE.
case hnm: (n == m).
- move/eqP: hnm => ->; rewrite homogeneous_includeE; exact: hom_m_projection.
- rewrite hom_finite_zeroE; apply: hom_m_degree (homogeneous_grade G n x).
  by rewrite hnm.
Qed.
(** Source for [homogeneous_include_homogeneous]: Federer (1969), 1.4.1, p.
    17, definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_include_homogeneous m (f : Hom_m W G m) :
  homogeneous (hom_finite_grading W G) m (homogeneous_include f).
Proof. by rewrite /homogeneous hom_finite_gradingE homogeneous_include_grade eqxx. Qed.
(** Source for [homogeneous_sum_decomposition]: Federer (1969), 1.4.1, p.
    17, definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_sum_decomposition f :
  exists N, f = \sum_(i < N) homogeneous_include (homogeneous_piece i f).
Proof.
have [N hN] := finite_hom_grade_finite f; exists N.
by under eq_bigr do rewrite homogeneous_pieceK.
Qed.
(** Source for [homogeneous_sum_induction]: Federer (1969), 1.4.1, p. 17,
    definition of A^*(V,W) and scalar abbreviations. In words: The full
    space of alternating forms is the direct sum of the spaces of forms of
    each degree; scalar-valued degree-m forms are called m-covectors.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma homogeneous_sum_induction (P : S -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
  (hH : forall m (f : Hom_m W G m), P (homogeneous_include f)) : forall f, P f.
Proof.
move=> f; have [N ->] := homogeneous_sum_decomposition f.
apply: big_ind => // i _; exact: hH.
Qed.
End HomogeneousSum.
