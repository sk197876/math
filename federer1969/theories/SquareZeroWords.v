(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP WordEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.1, third paragraph, in an arbitrary associative unital
    algebra: if f(v) f(v) = 0 for every v, the values of f anticommute,
    and a product f(v_1) ⋯ f(v_k) with a repeated vector vanishes. No
    restriction on the characteristic is needed. *)
Section SquareZeroWords.
Variable K : fieldType.
Variable V : lmodType K.
Variable A : algebra K.
Variable f : {linear V -> A}.
Hypothesis square_zero : forall v, alg_mul A (f v) (f v) = 0.
Local Notation mul := (alg_mul A).
Local Notation b := (alg_bilinear A).

(** Source for [square_zero_skew]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma square_zero_skew v w : mul (f v) (f w) = - mul (f w) (f v).
Proof.
have h := square_zero (v + w).
rewrite linearD (bilDl b) !(bilDr b) !square_zero add0r addr0 in h.
by apply/eqP; rewrite -addr_eq0; exact/eqP.
Qed.

(** Source for [square_zero_generator_word]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma square_zero_generator_word v (s : seq V) :
  mul (f v) (word_eval f s) = (-1 : K) ^+ size s *: mul (word_eval f s) (f v).
Proof.
elim: s => [|w s ih] /=.
  by rewrite alg_unitl alg_unitr scale1r.
rewrite alg_assoc square_zero_skew -scaleN1r (bilZl b) -alg_assoc ih
  (bilZr b) alg_assoc scalerA.
by rewrite exprS.
Qed.

(** Source for [square_zero_word_repeat]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma square_zero_word_repeat v (s t : seq V) :
  word_eval f (v :: s ++ v :: t) = 0.
Proof.
rewrite /= word_eval_cat /= alg_assoc square_zero_generator_word (bilZl b).
by rewrite -alg_assoc [mul (f v) (mul _ _)]alg_assoc square_zero (bil0l b) (bil0r b)
  scaler0.
Qed.

(** Source for [square_zero_word_nonuniq]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma square_zero_word_nonuniq (s : seq V) : ~~ uniq s -> word_eval f s = 0.
Proof.
elim: s => [|v s ih] //=.
case hv: (v \in s) => /=.
- move=> _; case/splitPr: hv => s1 s2.
  exact: square_zero_word_repeat.
- by move=> hs; rewrite (ih hs) (bil0r b).
Qed.
End SquareZeroWords.
