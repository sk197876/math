(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, opening identity Hom(V,W)=A^1(V,W), with both
    directions and cancellation laws. This holds for arbitrary W. *)
Section Identification.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [one_form]: Federer (1969), 1.4.4, p. 19, opening identity
    Hom(V,W)=A^1(V,W). In words: A linear map from V to W is precisely a
    W-valued one-form on V. Definition or construction used to formalise
    this passage. The one-form identification allows arbitrary W *)
Definition one_form (f : Hom V W) : A_m V W 1 :=
  hom_to_form (hom_of_linear (linear_comp (hom_as_linear f) (exterior_first_inverse V))).
(** Source for [one_formE]: Federer (1969), 1.4.4, p. 19, opening identity
    Hom(V,W)=A^1(V,W). In words: A linear map from V to W is precisely a
    W-valued one-form on V. Supporting lemma for this passage; not
    separately stated in the book. The one-form identification allows
    arbitrary W *)
Lemma one_formE f v : one_form f [tuple v] = f v.
Proof.
rewrite /one_form hom_to_formE hom_of_linearE.
change (f (exterior_degree_one V (exterior_word [:: v])) = f v).
rewrite exterior_word_cons exterior_word_nil.
change (f (exterior_degree_one V (wedge (exterior_generator v) (exterior_unit V))) = f v).
by rewrite wedge_unitr exterior_generatorK.
Qed.
(** Source for [one_form_linear]: Federer (1969), 1.4.4, p. 19, opening
    identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W is
    precisely a W-valued one-form on V. Supporting lemma for this passage;
    not separately stated in the book. The one-form identification allows
    arbitrary W *)
Lemma one_form_linear : linear one_form.
Proof.
move=> a f g; apply: form_ext => /tupleP [v t]; rewrite (tuple0 t).
by rewrite form_addE form_scaleE !one_formE hom_addE hom_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V W) (A_m V W 1)
  *:%R one_form one_form_linear.
(** Source for [one_formK]: Federer (1969), 1.4.4, p. 19, opening identity
    Hom(V,W)=A^1(V,W). In words: A linear map from V to W is precisely a
    W-valued one-form on V. Formalises the indicated part of the passage
    under the hypotheses in the statement below. The one-form identification
    allows arbitrary W *)
Lemma one_formK : cancel one_form (@one_hom K V W).
Proof. move=> f; apply: hom_ext => v; by rewrite one_homE one_formE. Qed.
(** Source for [one_homK]: Federer (1969), 1.4.4, p. 19, opening identity
    Hom(V,W)=A^1(V,W). In words: A linear map from V to W is precisely a
    W-valued one-form on V. Formalises the indicated part of the passage
    under the hypotheses in the statement below. The one-form identification
    allows arbitrary W *)
Lemma one_homK : cancel (@one_hom K V W) one_form.
Proof. move=> a; apply: one_hom_injective; exact: one_formK. Qed.
(** Source for [one_generator]: Federer (1969), 1.4.4, p. 19, opening
    identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W is
    precisely a W-valued one-form on V. Definition or construction used to
    formalise this passage. The one-form identification allows arbitrary W *)
Definition one_generator (f : Hom V W) : A_star V W := form_include (one_form f).
(** Source for [one_generator_linear]: Federer (1969), 1.4.4, p. 19, opening
    identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W is
    precisely a W-valued one-form on V. Supporting lemma for this passage;
    not separately stated in the book. The one-form identification allows
    arbitrary W *)
Lemma one_generator_linear : linear one_generator.
Proof. move=> a f g; by rewrite /one_generator !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V W) (A_star V W)
  *:%R one_generator one_generator_linear.
(** Source for [one_generator_homogeneous]: Federer (1969), 1.4.4, p. 19,
    opening identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W
    is precisely a W-valued one-form on V. Supporting lemma for this
    passage; not separately stated in the book. The one-form identification
    allows arbitrary W *)
Lemma one_generator_homogeneous f : homogeneous (A_star_grading V W) 1 (one_generator f).
Proof. exact: form_include_homogeneous. Qed.
(** Source for [one_generator_word]: Federer (1969), 1.4.4, p. 19, opening
    identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W is
    precisely a W-valued one-form on V. Supporting lemma for this passage;
    not separately stated in the book. The one-form identification allows
    arbitrary W *)
Lemma one_generator_word f s : one_generator f (exterior_word s) = form_words (one_form f) s.
Proof. by rewrite /one_generator form_includeE form_extensionE. Qed.
(** Source for [one_generatorE]: Federer (1969), 1.4.4, p. 19, opening
    identity Hom(V,W)=A^1(V,W). In words: A linear map from V to W is
    precisely a W-valued one-form on V. Supporting lemma for this passage;
    not separately stated in the book. The one-form identification allows
    arbitrary W *)
Lemma one_generatorE f v : one_generator f (exterior_generator v) = f v.
Proof. change (one_generator f (exterior_word [tuple v]) = f v); by rewrite one_generator_word form_wordsE one_formE. Qed.
End Identification.
