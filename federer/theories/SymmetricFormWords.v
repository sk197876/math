(** Federer (1969), 1.10.1, p. 44: supporting word extensions for symmetric
    forms. The word encoding is local infrastructure for the source's
    abstract factorisation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP PowerWords TensorAlgebraUP WordEvaluation
  AlternatingForms AlternatingWords SymmetricForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WordExtension.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
(** Source for [sform_words]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: Extend a form by zero on words of other lengths, to use the degree-wise universal property. *)
Definition sform_words (f : S_m V W m) := tuple_words f.
(** Source for [sform_wordsE]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: The word extension agrees with the form on an m-tuple. *)
Lemma sform_wordsE (f : S_m V W m) (t : m.-tuple V) : sform_words f t = f t.
Proof. exact: tuple_wordsE. Qed.
(** Source for [sform_words_wrong]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: The word extension vanishes on every other degree. *)
Lemma sform_words_wrong (f : S_m V W m) s : size s != m -> sform_words f s = 0.
Proof. exact: tuple_words_wrong. Qed.

(** Source for [sform_words_multilinear]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: Supporting step: extending by zero preserves multilinearity in word contexts. *)
Lemma sform_words_multilinear (f : S_m V W m) : multilinear_words (sform_words f).
Proof.
move=> s t a v w; case hs: (size (s ++ (0 : V) :: t) == m).
- change (tuple_words f (s ++ (a *: v + w) :: t) =
    a *: tuple_words f (s ++ v :: t) + tuple_words f (s ++ w :: t)).
  rewrite (@tuple_words_context K V W m f s t hs (a *: v + w))
    (@tuple_words_context K V W m f s t hs v) (@tuple_words_context K V W m f s t hs w).
  exact (@sform_multilinear K V W m f s t hs a v w).
- have hz u : size (s ++ u :: t) != m.
    by move: hs; rewrite !size_cat => ->.
  by rewrite !sform_words_wrong ?hz // scaler0 add0r.
Qed.

(** Source for [sform_words_symmetric]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: Supporting step: extending by zero preserves symmetry under rearranging the word. *)
Lemma sform_words_symmetric (f : S_m V W m) s t :
  perm_eq s t -> sform_words f s = sform_words f t.
Proof.
move=> hp; rewrite /sform_words /tuple_words.
case: insubP=> [u hu eu|hn]; case: insubP=> [v hv ev|hm].
- apply: sform_tuple_symmetric; by rewrite eu ev.
- by move: hm; rewrite -(perm_size hp) hu.
- by move: hn; rewrite (perm_size hp) hv.
- by [].
Qed.

(** Source for [sform_words_linear]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: The word extension depends linearly on the form. *)
Lemma sform_words_linear s : linear (fun f : S_m V W m => sform_words f s).
Proof.
move=> a f g; rewrite /sform_words /tuple_words.
case: (insub s : option (m.-tuple V)) => [t|].
- by rewrite sform_addE sform_scaleE.
- by rewrite scaler0 add0r.
Qed.

(** Source for [sform_of_words]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: Restrict a symmetric multilinear word function to actual m-tuples. *)
Definition sform_of_words (beta : seq V -> W)
    (hb : multilinear_words beta)
    (ha : forall s t, perm_eq s t -> beta s = beta t) : S_m V W m.
Proof.
apply: (@SymmetricForm K V W m (fun t => beta t)); apply/asboolP; split.
- move=> s t h; exact: hb s t.
- move=> s t ht; exact: ha ht.
Defined.

(** Source for [sform_of_wordsE]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: The restriction evaluates as the original word function. *)
Lemma sform_of_wordsE (beta : seq V -> W) hb ha (t : m.-tuple V) :
  sform_of_words (beta:=beta) hb ha t = beta t.
Proof. by []. Qed.
(** Source for [sform_of_wordsK]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: Restriction recovers the original form from its word extension. *)
Lemma sform_of_wordsK (f : S_m V W m) :
  sform_of_words (sform_words_multilinear f) (sform_words_symmetric f) = f.
Proof. apply: sform_ext => t; exact: sform_wordsE. Qed.

(** Source for [sform_wordsK]: Federer 1.10.1, p. 44,
    factorisation and homogeneous-Hom identifications. Supporting construction
    or lemma, in words: A symmetric multilinear word function supported in degree m is recovered from its restriction. *)
Lemma sform_wordsK (beta : seq V -> W) hb ha :
  (forall s, size s != m -> beta s = 0) ->
  forall s, sform_words (sform_of_words (beta:=beta) hb ha) s = beta s.
Proof.
move=> hz s; rewrite /sform_words /tuple_words.
case: insubP => [t ht he|hn].
- by rewrite sform_of_wordsE he.
- symmetry; exact: hz hn.
Qed.
End WordExtension.
