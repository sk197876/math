(** Federer (1969), 1.9.1, p. 41: products of generators in a commutative
    symmetric algebra are invariant under permutation. Supporting word
    calculation over arbitrary fields. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlgebraUP WordEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Words.
Variable K : fieldType.
Variable X : choiceType.
Variable A : algebra K.
Hypothesis hc : commutative (alg_mul A).
Variable f : X -> A.

(** Source for [commutative_word_permutation]: Federer 1.9.1,
    p. 41, commutativity paragraph. Supporting lemma: reordering
    a finite word does not change its product, including the empty word. *)
Lemma commutative_word_permutation (s t : seq X) :
  perm_eq s t -> word_eval f s = word_eval f t.
Proof.
apply/catCA_perm_subst: s t => s t u.
by rewrite !word_eval_cat !alg_assoc [alg_mul A (word_eval f s) (word_eval f t)]hc.
Qed.
End Words.
