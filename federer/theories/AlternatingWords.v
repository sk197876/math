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
From Federer Require Import AlternatingForms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.1: extend a function on V^m by zero on words of every
    other length. This connects the actual tuple domain with the tensor
    algebra's homogeneous-component universal property. *)
Section WordExtension.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.

(** Source for [tuple_words]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition tuple_words (f : m.-tuple V -> W) (s : seq V) : W :=
  if insub s : option (m.-tuple V) is Some t then f t else 0.
(** Source for [tuple_wordsE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tuple_wordsE f (t : m.-tuple V) : tuple_words f t = f t.
Proof. by rewrite /tuple_words valK. Qed.
(** Source for [tuple_words_wrong]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma tuple_words_wrong f s : size s != m -> tuple_words f s = 0.
Proof.
move=> hs; rewrite /tuple_words.
by rewrite (@insubF (seq V) (fun s => size s == m) _ s (negbTE hs)).
Qed.
(** Source for [tuple_words_context]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma tuple_words_context f s t h v :
  tuple_words f (s ++ v :: t) = f (context_tuple s t h v).
Proof. exact: (@tuple_wordsE f (context_tuple s t h v)). Qed.

(** Source for [form_words]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition form_words (f : A_m V W m) := tuple_words f.
(** Source for [form_wordsE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_wordsE (f : A_m V W m) (t : m.-tuple V) : form_words f t = f t.
Proof. exact: tuple_wordsE. Qed.
(** Source for [form_words_wrong]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_words_wrong (f : A_m V W m) s : size s != m -> form_words f s = 0.
Proof. exact: tuple_words_wrong. Qed.

(** Source for [form_words_multilinear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_words_multilinear (f : A_m V W m) : multilinear_words (form_words f).
Proof.
move=> s t a v w; case hs: (size (s ++ (0 : V) :: t) == m).
- change (tuple_words f (s ++ (a *: v + w) :: t) =
    a *: tuple_words f (s ++ v :: t) + tuple_words f (s ++ w :: t)).
  rewrite (@tuple_words_context f s t hs (a *: v + w))
    (@tuple_words_context f s t hs v) (@tuple_words_context f s t hs w).
  exact (@form_multilinear K V W m f s t hs a v w).
- have hz u : size (s ++ u :: t) != m.
    by move: hs; rewrite !size_cat => ->.
  by rewrite !form_words_wrong ?hz // scaler0 add0r.
Qed.

(** Source for [form_words_alternating]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_words_alternating (f : A_m V W m) s : ~~ uniq s -> form_words f s = 0.
Proof.
move=> hs; rewrite /form_words /tuple_words.
case: insubP => [t ht he|hn]; last by [].
apply: form_alternating; by rewrite he.
Qed.

(** Source for [form_words_linear]: Federer (1969), 1.4.1, p. 17,
    factorisation paragraph and first displayed isomorphism. In words: Every
    alternating m-linear map factors uniquely through the m-th exterior
    power, giving the isomorphism between forms and linear maps on that
    power. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma form_words_linear s : linear (fun f : A_m V W m => form_words f s).
Proof.
move=> a f g; rewrite /form_words /tuple_words.
case: (insub s : option (m.-tuple V)) => [t|].
- by rewrite form_addE form_scaleE.
- by rewrite scaler0 add0r.
Qed.

(** Source for [form_of_words]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Definition
    or construction used to formalise this passage. *)
Definition form_of_words (beta : seq V -> W)
    (hb : multilinear_words beta)
    (ha : forall s, ~~ uniq s -> beta s = 0) : A_m V W m.
Proof.
apply: (@AlternatingForm K V W m (fun t => beta t)); apply/asboolP; split.
- move=> s t h; exact: hb s t.
- move=> t ht; exact: ha ht.
Defined.

(** Source for [form_of_wordsE]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_of_wordsE (beta : seq V -> W) hb ha (t : m.-tuple V) :
  form_of_words (beta:=beta) hb ha t = beta t.
Proof. by []. Qed.
(** Source for [form_of_wordsK]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_of_wordsK (f : A_m V W m) :
  form_of_words (form_words_multilinear f) (form_words_alternating f) = f.
Proof. apply: form_ext => t; exact: form_wordsE. Qed.

(** Source for [form_wordsK]: Federer (1969), 1.4.1, p. 17, factorisation
    paragraph and first displayed isomorphism. In words: Every alternating
    m-linear map factors uniquely through the m-th exterior power, giving
    the isomorphism between forms and linear maps on that power. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma form_wordsK (beta : seq V -> W) hb ha :
  (forall s, size s != m -> beta s = 0) ->
  forall s, form_words (form_of_words (beta:=beta) hb ha) s = beta s.
Proof.
move=> hz s; rewrite /form_words /tuple_words.
case: insubP => [t ht he|hn].
- by rewrite form_of_wordsE he.
- symmetry; exact: hz hn.
Qed.
End WordExtension.
