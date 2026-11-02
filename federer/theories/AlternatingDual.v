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
  AlternatingExtension AlternatingIsomorphism AlternatingPairing BoundedHom
  HomogeneousSum HomFiniteFunctor AlternatingSum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, the dual-map paragraph: A^*(f,W) is the direct sum of
    A^m(f,W), characterised by the displayed pairing equation. *)
Section Dual.
Variable K : fieldType.
Variables V V' W : lmodType K.
Variable f : {linear V -> V'}.
Local Notation hf := (@exterior_algebra_map_graded K V V' f).
(** Source for [A_m_dual]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Definition or construction used to formalise this passage. *)
Definition A_m_dual m (phi : A_m V' W m) : A_m V W m :=
  homogeneous_form (homogeneous_precompose hf (form_homogeneous phi)).
(** Source for [A_star_dual]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Definition or construction used to formalise this passage. *)
Definition A_star_dual (phi : A_star V' W) : A_star V W := finite_precompose hf phi.
(** Source for [A_m_dual_linear]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma A_m_dual_linear m : linear (@A_m_dual m).
Proof. move=> a phi psi; by rewrite /A_m_dual !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (A_m V' W m) (A_m V W m)
  *:%R (@A_m_dual m) (@A_m_dual_linear m).
(** Source for [A_star_dual_linear]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma A_star_dual_linear : linear A_star_dual.
Proof. exact: finite_precompose_linear. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (A_star V' W) (A_star V W)
  *:%R A_star_dual A_star_dual_linear.
(** Source for [A_star_dualE]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma A_star_dualE phi x : A_star_dual phi x = phi (exterior_algebra_map f x).
Proof. by []. Qed.
(** Source for [A_m_dual_pairing]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma A_m_dual_pairing m (phi : A_m V' W m) x :
  pairing x (A_m_dual phi) = pairing (exterior_power_map f m x) phi.
Proof.
rewrite /pairing /form_to_hom /A_m_dual homogeneous_formK
  !homogeneous_restrictE homogeneous_precomposeE.
by [].
Qed.
(** Source for [A_m_dual_unique]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma A_m_dual_unique m (phi : A_m V' W m) (psi : A_m V W m) :
  (forall x, pairing x psi = pairing (exterior_power_map f m x) phi) -> psi = A_m_dual phi.
Proof. move=> h; apply: pairing_ext => x; by rewrite A_m_dual_pairing h. Qed.
(** Source for [A_m_dualE]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma A_m_dualE m (phi : A_m V' W m) (t : m.-tuple V) :
  A_m_dual phi t = phi (map_tuple f t).
Proof.
rewrite /A_m_dual homogeneous_formE homogeneous_precomposeE
  exterior_algebra_map_word form_homogeneousE form_extensionE.
exact: (form_wordsE phi (map_tuple f t)).
Qed.
(** Source for [A_star_dual_include]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma A_star_dual_include m (phi : A_m V' W m) :
  A_star_dual (form_include phi) = form_include (A_m_dual phi).
Proof.
by rewrite /A_star_dual /form_include /A_m_dual homogeneous_formK finite_precompose_include.
Qed.
(** Source for [A_star_dual_component]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma A_star_dual_component m phi :
  form_component m (A_star_dual phi) = A_m_dual (form_component m phi).
Proof.
by rewrite /A_star_dual /A_m_dual /form_component homogeneous_formK finite_precompose_piece.
Qed.
(** Source for [A_star_dual_graded]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma A_star_dual_graded : preserves_grading (A_star_grading V' W) (A_star_grading V W) A_star_dual.
Proof.
move=> m phi hphi; change (finite_hom_grade m (A_star_dual phi) = A_star_dual phi).
rewrite -finite_precompose_grade; exact (congr1 A_star_dual hphi).
Qed.
(** Source for [A_star_dual_direct_sum]: Federer (1969), 1.4.1, pp. 17-18,
    dual-map paragraph and characterising pairing identity. In words: A
    linear map induces a contravariant map on forms, degree by degree;
    pairing with its pullback equals pairing the induced exterior image with
    the original form. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem A_star_dual_direct_sum phi : exists N,
  A_star_dual phi = \sum_(i < N) form_include (A_m_dual (form_component i phi)).
Proof.
have [N hN] := alternating_sum_decomposition phi; exists N.
rewrite {1}hN linear_sum; apply: eq_bigr => i _; exact: A_star_dual_include.
Qed.
End Dual.

(** Federer 1.4.1: A^*f abbreviates A^*(f,K). *)
(** Source for [A_dual]: Federer (1969), 1.4.1, pp. 17-18, dual-map
    paragraph and characterising pairing identity. In words: A linear map
    induces a contravariant map on forms, degree by degree; pairing with its
    pullback equals pairing the induced exterior image with the original
    form. Definition or construction used to formalise this passage. *)
Definition A_dual (K : fieldType) (V V' : lmodType K) (f : {linear V -> V'}) :=
  @A_star_dual K V V' K^o f.
Arguments A_dual {K V V'} f.

(** Federer 1.4.1, final paragraph and its entire chain of equalities.
    A basis of n vectors expresses the hypothesis dim V=n; the scalar
    det(f) is the intrinsic determinant constructed in 1.3.4. Coefficients
    may lie in any vector space W. *)
Section TopDual.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n : nat.
Variables V W : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> V}.
Local Notation d := (det h2 he f).
(** Source for [top_dual_pairing]: Federer (1969), 1.4.1, p. 18, example
    preceding 1.4.2. In words: Pullback by an endomorphism acts on forms in
    the top degree by multiplication by its determinant. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma top_dual_pairing (phi : A_m V W n) x :
  [ /\ pairing x (A_m_dual f phi) = pairing (exterior_power_map f n x) phi,
       pairing (exterior_power_map f n x) phi = pairing (d *: x) phi &
       pairing (d *: x) phi = pairing x (d *: phi) ].
Proof.
split.
- exact: A_m_dual_pairing.
- by rewrite (detE h2 he).
- by rewrite (bilZl (@pairing_bilinear K V W n)) (bilZr (@pairing_bilinear K V W n)).
Qed.
(** Source for [A_m_dual_det]: Federer (1969), 1.4.1, p. 18, example
    preceding 1.4.2. In words: Pullback by an endomorphism acts on forms in
    the top degree by multiplication by its determinant. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem A_m_dual_det (phi : A_m V W n) : A_m_dual f phi = d *: phi.
Proof.
apply: pairing_ext => x; have [h1 h2' h3] := top_dual_pairing phi x.
exact (eq_trans h1 (eq_trans h2' h3)).
Qed.
End TopDual.
