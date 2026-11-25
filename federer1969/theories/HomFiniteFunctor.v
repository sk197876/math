(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP GradedAlgebra GradedSums.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.1: precomposition by a graded map
    preserves homogeneous degree and finite homogeneous support. *)
Section Precomposition.
Variable K : fieldType.
Variables U V W : lmodType K.
Variables (G : grading U) (H : grading V).
Variable f : {linear U -> V}.
Hypothesis hf : preserves_grading G H f.

(** Source for [graded_map_projection]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma graded_map_projection m x : f (grade G m x) = grade H m (f x).
Proof.
elim/(graded_induction (G:=G)): x => [|x y hx hy|n x hx].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite (grade_homogeneous m hx) (grade_homogeneous m (hf hx)).
  by case: (m == n); rewrite ?linear0.
Qed.

(** Source for [homogeneous_precomposition_degree]: Federer (1969), 1.4.1,
    pp. 17-18, dual-map paragraph and characterising pairing identity. In
    words: A linear map induces a contravariant map on forms, degree by
    degree; pairing with its pullback equals pairing the induced exterior
    image with the original form. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma homogeneous_precomposition_degree m (a : Hom_m W H m) :
  hom_degree G m (hom_comp a (hom_of_linear f)).
Proof.
move=> n x hn hx; rewrite hom_compE hom_of_linearE.
apply: hom_m_degree hn (hf hx).
Qed.
(** Source for [homogeneous_precompose]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Definition or construction used to formalise this
    passage. *)
Definition homogeneous_precompose m (a : Hom_m W H m) : Hom_m W G m :=
  @HomogeneousHom K U W G m (hom_comp a (hom_of_linear f))
    (introT (asboolP _) (homogeneous_precomposition_degree a)).
(** Source for [homogeneous_precomposeE]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma homogeneous_precomposeE m (a : Hom_m W H m) x : homogeneous_precompose a x = a (f x).
Proof. by []. Qed.
(** Source for [homogeneous_precompose_linear]: Federer (1969), 1.4.1, pp.
    17-18, dual-map paragraph and characterising pairing identity. In words:
    A linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma homogeneous_precompose_linear m : linear (@homogeneous_precompose m).
Proof. move=> c a b; apply: hom_m_ext => x; by []. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (Hom_m W H m) (Hom_m W G m)
  *:%R (@homogeneous_precompose m) (@homogeneous_precompose_linear m).

(** Source for [finite_precomposition_finite]: Federer (1969), 1.4.1, pp.
    17-18, dual-map paragraph and characterising pairing identity. In words:
    A linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precomposition_finite (a : Hom_finite W H) :
  hom_finite_pred G (hom_comp a (hom_of_linear f)).
Proof.
apply/asboolP; have [N hN] := hom_finite_bound a; exists N.
move=> n x hn hx; rewrite hom_compE hom_of_linearE; exact: hN hn (hf hx).
Qed.
(** Source for [finite_precompose]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Definition or construction used to formalise this
    passage. *)
Definition finite_precompose (a : Hom_finite W H) : Hom_finite W G :=
  @FiniteHom K U W G (hom_comp a (hom_of_linear f)) (finite_precomposition_finite a).
(** Source for [finite_precomposeE]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precomposeE a x : finite_precompose a x = a (f x).
Proof. by []. Qed.
(** Source for [finite_precompose_linear]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precompose_linear : linear finite_precompose.
Proof. move=> c a b; apply: hom_finite_ext => x; by []. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom_finite W H) (Hom_finite W G)
  *:%R finite_precompose finite_precompose_linear.
(** Source for [finite_precompose_grade]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precompose_grade m a :
  finite_precompose (finite_hom_grade m a) = finite_hom_grade m (finite_precompose a).
Proof.
apply: hom_finite_ext => x.
by rewrite !finite_precomposeE !finite_hom_gradeE finite_precomposeE graded_map_projection.
Qed.
(** Source for [finite_precompose_include]: Federer (1969), 1.4.1, pp.
    17-18, dual-map paragraph and characterising pairing identity. In words:
    A linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precompose_include m (a : Hom_m W H m) :
  finite_precompose (homogeneous_include a) = homogeneous_include (homogeneous_precompose a).
Proof. apply: hom_finite_ext => x; by []. Qed.
(** Source for [finite_precompose_piece]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_precompose_piece m a :
  homogeneous_piece m (finite_precompose a) = homogeneous_precompose (homogeneous_piece m a).
Proof.
apply: hom_m_ext => x.
by rewrite !homogeneous_pieceE !finite_precomposeE homogeneous_precomposeE homogeneous_pieceE graded_map_projection.
Qed.
End Precomposition.
