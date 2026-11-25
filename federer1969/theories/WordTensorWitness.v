(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra FamilyUpdate
  TensorFamilyUP WordEvaluation PowerWords TensorAlgebraUP WordTensorAlgebra
  WordTensorGrading WordTensorPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Existence of a tensor algebra (Federer 1.2.3): the quotient of the word
    algebra satisfies [is_graded_tensor_algebra]. The construction is used
    only through [word_tensor_algebra_exists]. *)
Section Witness.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [word_generator]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_generator : {linear V -> tensor_algebra V} :=
  GRing.Linear.clone _ _ _ _ (@tensor_generator K V) _.

(** Source for [word_eval_generator]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_eval_generator s : word_eval word_generator s = tensor_word s.
Proof.
elim: s => [|v s ih] //=.
by rewrite ih; exact: tensor_product_words [:: v] s.
Qed.

(** Source for [word_degree_universal]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_degree_universal m : degree_universal word_generator (tensor_grading V) m.
Proof.
move=> Z beta hb.
have [f [hf [hdeg hu]]] :=
  tensor_power_universal (beta_words_multilinear hb) (@beta_words_zero K V m Z beta).
exists f; split; first exact: hdeg.
split.
  by move=> x; rewrite /algebra_power word_eval_generator hf beta_words_power.
move=> g hg hgx; apply: hu => s.
case: (eqVneq (size s) m) => hs.
  rewrite /beta_words hs eqxx -{1}(power_seq_to_power hs) -word_eval_generator.
  exact: hgx.
rewrite beta_words_zero // -hg.
have -> : grade (tensor_grading V) m (tensor_word s) = tensor_degree m (tensor_word s) by [].
rewrite tensor_degree_word (negPf hs).
exact: linear0.
Qed.

(** Source for [word_tensor_algebra_exists]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem word_tensor_algebra_exists :
  is_graded_tensor_algebra word_generator (tensor_grading V).
Proof.
constructor; last exact: word_degree_universal.
move=> m x; rewrite /algebra_power word_eval_generator.
by have := tensor_word_homogeneous (power_seq x); rewrite size_power_seq.
Qed.
End Witness.
