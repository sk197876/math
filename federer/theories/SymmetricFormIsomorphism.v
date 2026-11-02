(** Federer (1969), 1.10.1, p. 44: the two linear isomorphisms between
    symmetric forms, maps on a symmetric power and homogeneous maps on the
    full algebra. Both inverse identities are proved; arbitrary fields,
    dimensions and degree zero are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP WordEvaluation GradedAlgebra GradedComponents
  Hom HomogeneousHom SymmetricAlgebra SymmetricGrading
  SymmetricForms SymmetricFormWords SymmetricFormExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Isomorphism.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).
Local Notation A := (S_m V W m).
Local Notation H := (Hom_m W G m).
Local Notation P := (symmetric_power V m).
(** Source for [symmetric_homogeneous_words]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Evaluate a homogeneous linear map on products of generating vectors. *)
Definition symmetric_homogeneous_words (h : H) s := h (symmetric_word s).
(** Source for [symmetric_homogeneous_words_multilinear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The resulting word function is multilinear. *)
Lemma symmetric_homogeneous_words_multilinear (h : H) : multilinear_words (symmetric_homogeneous_words h).
Proof.
move=> s t a v w; rewrite /symmetric_homogeneous_words /symmetric_word (word_eval_multilinear _ s t a v w).
exact: hom_linear.
Qed.
(** Source for [symmetric_homogeneous_words_symmetric]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The word function is symmetric because symmetric multiplication is commutative. *)
Lemma symmetric_homogeneous_words_symmetric (h : H) s t :
  perm_eq s t -> symmetric_homogeneous_words h s = symmetric_homogeneous_words h t.
Proof. move=> hp; by rewrite /symmetric_homogeneous_words (symmetric_word_permutation hp). Qed.
(** Source for [symmetric_homogeneous_words_wrong]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The word function vanishes at all lengths other than m. *)
Lemma symmetric_homogeneous_words_wrong (h : H) s : size s != m -> symmetric_homogeneous_words h s = 0.
Proof. move=> hs; apply: hom_m_degree (symmetric_word_homogeneous s); exact: hs. Qed.
(** Source for [homogeneous_sform]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Restrict the homogeneous linear map to products of m generating vectors, giving a symmetric form. *)
Definition homogeneous_sform (h : H) : A :=
  sform_of_words m (symmetric_homogeneous_words_multilinear h) (symmetric_homogeneous_words_symmetric h).
(** Source for [homogeneous_sformE]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The form evaluates as the linear map on the corresponding product. *)
Lemma homogeneous_sformE h (t : m.-tuple V) : homogeneous_sform h t = h (symmetric_word t).
Proof. by []. Qed.
(** Source for [homogeneous_sform_wordsE]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Extending that form by zero recovers evaluation on every word. *)
Lemma homogeneous_sform_wordsE h s : sform_words (homogeneous_sform h) s = h (symmetric_word s).
Proof.
exact (@sform_wordsK K V W m (symmetric_homogeneous_words h)
  (symmetric_homogeneous_words_multilinear h) (symmetric_homogeneous_words_symmetric h)
  (@symmetric_homogeneous_words_wrong h) s).
Qed.
(** Source for [homogeneous_sform_linear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Restriction to symmetric forms is linear. *)
Lemma homogeneous_sform_linear : linear homogeneous_sform.
Proof.
move=> a h k; apply: sform_ext => t.
by rewrite homogeneous_sformE hom_m_addE hom_m_scaleE sform_addE sform_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K H A
  *:%R homogeneous_sform homogeneous_sform_linear.

(** Source for [sform_homogeneousK]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Extension followed by restriction recovers the form. *)
Lemma sform_homogeneousK : cancel (@sform_homogeneous K V W m) homogeneous_sform.
Proof.
move=> f; apply: sform_ext => t.
by rewrite homogeneous_sformE sform_homogeneousE sform_extensionE sform_wordsE.
Qed.
(** Source for [homogeneous_sformK]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Restriction followed by extension recovers the homogeneous linear map. *)
Lemma homogeneous_sformK : cancel homogeneous_sform (@sform_homogeneous K V W m).
Proof.
move=> h; apply: hom_m_ext => x.
change (sform_extension (homogeneous_sform h) x = h x).
elim/symmetric_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- rewrite !linearD; exact (congr2 +%R hx hy).
- rewrite !linearZ; exact (congr1 (fun y : W => a *: y) hx).
- by rewrite sform_extensionE homogeneous_sform_wordsE.
Qed.

(** Source for [sform_to_hom]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Restrict the homogeneous extension to the m-th symmetric power. *)
Definition sform_to_hom (f : A) : Hom P W := homogeneous_restrict (sform_homogeneous f).
(** Source for [hom_to_sform]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: Extend a linear map from the m-th power by zero in other degrees, and restrict to tuples. *)
Definition hom_to_sform (h : Hom P W) : A := homogeneous_sform (homogeneous_extend h).
(** Source for [sform_to_homE]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The linear map evaluates on a component by the form extension. *)
Lemma sform_to_homE f x : sform_to_hom f x = sform_extension f (component_val x).
Proof. by []. Qed.
(** Source for [sform_to_hom_linear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The map from forms to Hom is linear. *)
Lemma sform_to_hom_linear : linear sform_to_hom.
Proof. move=> a f g; by rewrite /sform_to_hom !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K A (Hom P W)
  *:%R sform_to_hom sform_to_hom_linear.
(** Source for [hom_to_sform_linear]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The inverse map from Hom to forms is linear. *)
Lemma hom_to_sform_linear : linear hom_to_sform.
Proof. move=> a f g; by rewrite /hom_to_sform !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom P W) A
  *:%R hom_to_sform hom_to_sform_linear.
(** Source for [sform_to_homK]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The first inverse identity of the displayed isomorphism. *)
Lemma sform_to_homK : cancel sform_to_hom hom_to_sform.
Proof. move=> f; by rewrite /sform_to_hom /hom_to_sform homogeneous_restrictK sform_homogeneousK. Qed.
(** Source for [hom_to_sformK]: Federer 1.10.1, p. 44,
    the two displayed Hom identifications. In words: The second inverse identity of the displayed isomorphism. *)
Lemma hom_to_sformK : cancel hom_to_sform sform_to_hom.
Proof. move=> h; by rewrite /sform_to_hom /hom_to_sform homogeneous_sformK homogeneous_extendK. Qed.

(** Source for [symmetric_tuple_component]: Federer 1.10.1,
    p. 44, the product v_1 ... v_m in the m-th symmetric power. *)
Definition symmetric_tuple_component (t : m.-tuple V) : P :=
  component G m (symmetric_word t).

(** Source for [symmetric_tuple_componentE]: Federer 1.10.1,
    p. 44, supporting identification of that component with its word. *)
Lemma symmetric_tuple_componentE (t : m.-tuple V) :
  component_val (symmetric_tuple_component t) = symmetric_word t.
Proof.
rewrite /symmetric_tuple_component componentE.
change (symmetric_degree m (symmetric_word t) = symmetric_word t).
by rewrite symmetric_degree_word size_tuple eqxx.
Qed.

(** Source for [sform_to_hom_tuple]: Federer 1.10.1, p. 44,
    the displayed equation characterising the form-to-Hom isomorphism:
    f(v_1,...,v_m)=h(v_1 ... v_m). *)
Lemma sform_to_hom_tuple f (t : m.-tuple V) :
  sform_to_hom f (symmetric_tuple_component t) = f t.
Proof.
by rewrite sform_to_homE symmetric_tuple_componentE sform_extensionE sform_wordsE.
Qed.

(** Source for [hom_to_sformE]: Federer 1.10.1, p. 44,
    the inverse isomorphism evaluates a linear map on products of vectors. *)
Lemma hom_to_sformE h (t : m.-tuple V) :
  hom_to_sform h t = h (symmetric_tuple_component t).
Proof. by rewrite /hom_to_sform homogeneous_sformE homogeneous_extendE. Qed.

(** Source for [represents_sform]: Federer 1.10.1, p. 44,
    the displayed equation relating a symmetric form and its linear map. *)
Definition represents_sform (f : A) (h : Hom P W) :=
  forall t : m.-tuple V, h (symmetric_tuple_component t) = f t.

(** Source for [sform_to_hom_represents]: Federer 1.10.1,
    p. 44, the canonical linear map represents the form. *)
Lemma sform_to_hom_represents f : represents_sform f (sform_to_hom f).
Proof. exact: sform_to_hom_tuple. Qed.

(** Source for [represents_sform_unique]: Federer 1.10.1,
    p. 44, the linear map representing a form is unique. *)
Lemma represents_sform_unique f h : represents_sform f h -> h = sform_to_hom f.
Proof.
move=> hh; have he : hom_to_sform h = f.
  apply: sform_ext=> t; by rewrite hom_to_sformE hh.
by rewrite -he hom_to_sformK.
Qed.

(** Source for [symmetric_form_universal]: Federer 1.10.1, p. 44, the
    universal factorisation underlying the first linear isomorphism. *)
Theorem symmetric_form_universal f : exists! h : Hom P W, represents_sform f h.
Proof.
exists (sform_to_hom f); split; first exact: sform_to_hom_represents.
move=> h hh; symmetry; exact: represents_sform_unique hh.
Qed.
End Isomorphism.
