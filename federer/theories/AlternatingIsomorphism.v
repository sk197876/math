(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import Exterior TensorPowers.
From Federer Require Import Hom HomogeneousHom AlternatingForms
  AlternatingWords AlternatingExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1, first paragraph and the two displayed isomorphisms.
    All three spaces are constructed vector spaces. The maps below are
    linear and have both inverse laws, including in degree zero. *)
Section Isomorphism.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).
Local Notation A := (A_m V W m).
Local Notation H := (Hom_m W G m).
Local Notation P := (exterior_power V m).

(** Source for [homogeneous_words]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Definition or construction used to
    formalise this passage. *)
Definition homogeneous_words (h : H) s := h (exterior_word s).
(** Source for [homogeneous_words_multilinear]: Federer (1969), 1.4.1, p.
    17, second displayed isomorphism. In words: Forms of degree m identify
    with linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_words_multilinear (h : H) : multilinear_words (homogeneous_words h).
Proof.
move=> s t a v w; rewrite /homogeneous_words (exterior_word_context_linear s t a v w).
exact: hom_linear.
Qed.
(** Source for [homogeneous_words_alternating]: Federer (1969), 1.4.1, p.
    17, second displayed isomorphism. In words: Forms of degree m identify
    with linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_words_alternating (h : H) s : ~~ uniq s -> homogeneous_words h s = 0.
Proof. move=> hs; by rewrite /homogeneous_words (exterior_word_nonuniq hs) linear0. Qed.
(** Source for [homogeneous_words_wrong]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_words_wrong (h : H) s : size s != m -> homogeneous_words h s = 0.
Proof. move=> hs; apply: hom_m_degree (exterior_word_homogeneous s); exact: hs. Qed.
(** Source for [homogeneous_form]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Definition or construction used to
    formalise this passage. *)
Definition homogeneous_form (h : H) : A :=
  form_of_words m (homogeneous_words_multilinear h) (homogeneous_words_alternating h).
(** Source for [homogeneous_formE]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_formE h (t : m.-tuple V) : homogeneous_form h t = h (exterior_word t).
Proof. by []. Qed.
(** Source for [homogeneous_form_wordsE]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_form_wordsE h s : form_words (homogeneous_form h) s = h (exterior_word s).
Proof.
exact (@form_wordsK K V W m (homogeneous_words h)
  (homogeneous_words_multilinear h) (homogeneous_words_alternating h)
  (@homogeneous_words_wrong h) s).
Qed.
(** Source for [homogeneous_form_linear]: Federer (1969), 1.4.1, p. 17,
    second displayed isomorphism. In words: Forms of degree m identify with
    linear maps on the whole exterior algebra that vanish on every
    homogeneous component of degree different from m. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma homogeneous_form_linear : linear homogeneous_form.
Proof.
move=> a h k; apply: form_ext => t.
by rewrite homogeneous_formE hom_m_addE hom_m_scaleE form_addE form_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K H A
  *:%R homogeneous_form homogeneous_form_linear.

(** Source for [form_homogeneousK]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma form_homogeneousK : cancel (@form_homogeneous K V W m) homogeneous_form.
Proof.
move=> f; apply: form_ext => t.
by rewrite homogeneous_formE form_homogeneousE form_extensionE form_wordsE.
Qed.
(** Source for [homogeneous_formK]: Federer (1969), 1.4.1, p. 17, second
    displayed isomorphism. In words: Forms of degree m identify with linear
    maps on the whole exterior algebra that vanish on every homogeneous
    component of degree different from m. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma homogeneous_formK : cancel homogeneous_form (@form_homogeneous K V W m).
Proof.
move=> h; apply: hom_m_ext => x.
change (form_extension (homogeneous_form h) x = h x).
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite !linearZ; exact (congr1 (fun y : W => a *: y) hx).
- by rewrite form_extensionE homogeneous_form_wordsE.
Qed.

(** Source for [form_to_hom]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition form_to_hom (f : A) : Hom P W := homogeneous_restrict (form_homogeneous f).
(** Source for [hom_to_form]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition hom_to_form (h : Hom P W) : A := homogeneous_form (homogeneous_extend h).
(** Source for [form_to_homE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_to_homE f x : form_to_hom f x = form_extension f (component_val x).
Proof. by []. Qed.
(** Source for [form_to_hom_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_to_hom_linear : linear form_to_hom.
Proof. move=> a f g; by rewrite /form_to_hom !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K A (Hom P W)
  *:%R form_to_hom form_to_hom_linear.
(** Source for [hom_to_form_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma hom_to_form_linear : linear hom_to_form.
Proof. move=> a f g; by rewrite /hom_to_form !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom P W) A
  *:%R hom_to_form hom_to_form_linear.
(** Source for [form_to_homK]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_to_homK : cancel form_to_hom hom_to_form.
Proof. move=> f; by rewrite /form_to_hom /hom_to_form homogeneous_restrictK form_homogeneousK. Qed.
(** Source for [hom_to_formK]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_to_formK : cancel hom_to_form form_to_hom.
Proof. move=> h; by rewrite /form_to_hom /hom_to_form homogeneous_formK homogeneous_extendK. Qed.

(** Source for [exterior_tuple_component]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_tuple_component (t : m.-tuple V) :
  component G m (exterior_word t) = e_lambda idfun t.
Proof.
apply: val_inj; change (exterior_degree m (exterior_word t) = exterior_word [seq i | i <- t]).
by rewrite exterior_degree_word size_tuple eqxx map_id.
Qed.
(** Source for [form_to_hom_tuple]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_to_hom_tuple f (t : m.-tuple V) : form_to_hom f (e_lambda idfun t) = f t.
Proof. by rewrite form_to_homE e_lambdaE map_id form_extensionE form_wordsE. Qed.
(** Source for [hom_to_formE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma hom_to_formE h (t : m.-tuple V) : hom_to_form h t = h (e_lambda idfun t).
Proof. by rewrite /hom_to_form homogeneous_formE homogeneous_extendE exterior_tuple_component. Qed.

(** The unique map h in Federer's first displayed formula. *)
(** Source for [represents_form]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Definition or construction used to formalise this passage. *)
Definition represents_form (f : A) (h : Hom P W) :=
  forall t : m.-tuple V, h (e_lambda idfun t) = f t.
(** Source for [form_to_hom_represents]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_to_hom_represents f : represents_form f (form_to_hom f).
Proof. exact: form_to_hom_tuple. Qed.
(** Source for [represents_form_unique]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma represents_form_unique f h : represents_form f h -> h = form_to_hom f.
Proof.
move=> hh; have he : hom_to_form h = f.
  apply: form_ext => t; by rewrite hom_to_formE hh.
by rewrite -he hom_to_formK.
Qed.
(** Source for [alternating_form_universal]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem alternating_form_universal f : exists! h : Hom P W, represents_form f h.
Proof.
exists (form_to_hom f); split; first exact: form_to_hom_represents.
move=> h hh; symmetry; exact: represents_form_unique hh.
Qed.

(** The tensor-power map g and the exterior-power map h form the quotient
    factorisation stated immediately before the first isomorphism. *)
(** Source for [form_tensor_power_tuple]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_tensor_power_tuple (f : A) (t : m.-tuple V) :
  form_tensor_power f (component (tensor_grading V) m (tensor_word t)) = f t.
Proof.
change (form_tensor f (tensor_degree m (tensor_word t)) = f t).
by rewrite tensor_degree_word size_tuple eqxx form_tensorE form_wordsE.
Qed.
(** Source for [form_quotient_factorisation]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma form_quotient_factorisation f x :
  form_to_hom f (exterior_power_projection V m x) = form_tensor_power f x.
Proof.
rewrite form_to_homE exterior_power_projectionE.
exact: form_extension_projection.
Qed.
End Isomorphism.
