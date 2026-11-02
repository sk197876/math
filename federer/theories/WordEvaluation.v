(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Products f(x_1) ⋯ f(x_k) in an associative unital algebra, the empty
    product being the unit. These notions do not depend on a tensor algebra. *)
Section WordEvaluation.
Variable K : fieldType.
Variable X : choiceType.
Variable A : algebra K.
Variable f : X -> A.

(** Source for [word_eval]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Fixpoint word_eval (s : seq X) : A :=
  if s is x :: t then alg_mul A (f x) (word_eval t) else alg_one A.

(** Source for [word_eval_cat]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_eval_cat s t :
  word_eval (s ++ t) = alg_mul A (word_eval s) (word_eval t).
Proof.
elim: s => [|x s ih] /=; first by rewrite alg_unitl.
by rewrite ih alg_assoc.
Qed.
End WordEvaluation.

(** A function on finite sequences is multilinear if it is linear in each
    position, the other entries being fixed. *)
Section MultilinearWords.
Variable K : fieldType.
Variable V : lmodType K.
Variable Z : lmodType K.

(** Source for [multilinear_words]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition multilinear_words (beta : seq V -> Z) : Prop :=
  forall s t, linear (fun v : V => beta (s ++ v :: t)).
End MultilinearWords.

(** Source for [word_eval_multilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_eval_multilinear (K : fieldType) (V : lmodType K) (A : algebra K)
    (f : {linear V -> A}) :
  multilinear_words (word_eval f).
Proof.
move=> s t a v w; rewrite !word_eval_cat /= linearP.
have [hl hr] := alg_bilinear A.
by rewrite (hl (word_eval f t)) (hr (word_eval f s)).
Qed.
