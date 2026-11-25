(** Federer (1969), 1.10.1, p. 44: the graded direct sum of symmetric forms.
    The homogeneous-Hom model is justified by the preceding proved linear
    isomorphisms. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import GradedAlgebra Hom HomogeneousHom BoundedHom
  HomogeneousSum SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SymmetricFormSum.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [S_star]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: The graded space of symmetric forms is the direct sum of the spaces of each degree. It is realised by bounded homogeneous linear maps using the proved isomorphisms. *)
Definition S_star := Hom_finite W (symmetric_grading V).
(** Source for [S_star_grading]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: The grading extracts each homogeneous form component. *)
Definition S_star_grading : grading S_star := hom_finite_grading W (symmetric_grading V).
(** Source for [sform_include]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Include a form of degree m in the direct sum. *)
Definition sform_include m (f : S_m V W m) : S_star := homogeneous_include (sform_homogeneous f).
(** Source for [sform_component]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Extract the degree-m symmetric form. *)
Definition sform_component m (f : S_star) : S_m V W m := homogeneous_sform (homogeneous_piece m f).
(** Source for [sform_includeE]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Inclusion evaluates as the form extension on the full symmetric algebra. *)
Lemma sform_includeE m (f : S_m V W m) x : sform_include f x = sform_extension f x.
Proof. by []. Qed.
(** Source for [sform_componentE]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: The degree-m component evaluates on an m-tuple as the full map on its product. *)
Lemma sform_componentE m f (t : m.-tuple V) : sform_component m f t = f (symmetric_word t).
Proof.
rewrite /sform_component homogeneous_sformE homogeneous_pieceE.
change (f (symmetric_degree m (symmetric_word t)) = f (symmetric_word t)).
by rewrite symmetric_degree_word size_tuple eqxx.
Qed.
(** Source for [sform_include_linear]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Inclusion of one degree is linear. *)
Lemma sform_include_linear m : linear (@sform_include m).
Proof. move=> a f g; by rewrite /sform_include !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (S_m V W m) S_star
  *:%R (@sform_include m) (@sform_include_linear m).
(** Source for [sform_component_linear]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Extraction of a component is linear. *)
Lemma sform_component_linear m : linear (sform_component m).
Proof. move=> a f g; by rewrite /sform_component !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K S_star (S_m V W m)
  *:%R (sform_component m) (sform_component_linear m).
(** Source for [sform_includeK]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Extracting the included degree recovers the original form. *)
Lemma sform_includeK m : cancel (@sform_include m) (sform_component m).
Proof. move=> f; by rewrite /sform_include /sform_component homogeneous_includeK sform_homogeneousK. Qed.
(** Source for [sform_componentK]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Including an extracted form gives the grading projection. *)
Lemma sform_componentK m f : sform_include (sform_component m f) = grade S_star_grading m f.
Proof.
by rewrite /sform_include /sform_component homogeneous_sformK homogeneous_pieceK.
Qed.
(** Source for [sform_include_grade]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Distinct degree projections are orthogonal. *)
Lemma sform_include_grade n m (f : S_m V W m) :
  grade S_star_grading n (sform_include f) = if n == m then sform_include f else 0.
Proof. exact: homogeneous_include_grade. Qed.
(** Source for [sform_include_homogeneous]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: An included m-form is homogeneous of degree m. *)
Lemma sform_include_homogeneous m (f : S_m V W m) :
  homogeneous S_star_grading m (sform_include f).
Proof. by rewrite /homogeneous sform_include_grade eqxx. Qed.
(** Source for [symmetric_form_sum_decomposition]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Every element is a finite sum of its homogeneous forms. *)
Theorem symmetric_form_sum_decomposition f : exists N,
  f = \sum_(i < N) sform_include (sform_component i f).
Proof.
have [N hN] := grade_finite S_star_grading f; exists N.
by under eq_bigr do rewrite sform_componentK.
Qed.
(** Source for [symmetric_form_sum_ext]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: All homogeneous form components determine an element uniquely. *)
Lemma symmetric_form_sum_ext (f g : S_star) :
  (forall m, sform_component m f = sform_component m g) -> f = g.
Proof.
move=> h; apply: hom_finite_ext => x.
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite !linearZ; exact (congr1 (fun y : W => a *: y) hx).
- have he := congr1 (fun a : S_m V W (size s) => a (in_tuple s)) (h (size s)).
  by rewrite !sform_componentE in he.
Qed.
(** Source for [symmetric_form_sum_induction]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Supporting induction on a finite sum of homogeneous forms. *)
Lemma symmetric_form_sum_induction (P : S_star -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
  (hF : forall m (f : S_m V W m), P (sform_include f)) : forall f, P f.
Proof.
move=> f; have [N ->] := symmetric_form_sum_decomposition f.
apply: big_ind => // i _; exact: hF.
Qed.
End SymmetricFormSum.
Arguments S_star {K} V W.

(** Source for [symmetric_covector]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Abbreviation for scalar-valued homogeneous symmetric forms. *)
Definition symmetric_covector (K : fieldType) (V : lmodType K) m := S_m V K^o m.
(** Source for [S_symmetric_covectors]: Federer 1.10.1, p. 44,
    direct-sum definition and scalar abbreviations. In words: Abbreviation for the full graded space of scalar-valued symmetric forms. *)
Definition S_symmetric_covectors (K : fieldType) (V : lmodType K) := S_star V K^o.
Arguments symmetric_covector {K} V m.
Arguments S_symmetric_covectors {K} V.
