(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra
  ExteriorAlgebra ExteriorGrading.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Anticommutativity.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation wb := (wedge_bilinear V).
Local Notation E := (exterior_space V).

(** Federer 1.3.1, third paragraph: move a vector past a product, one
    adjacent interchange at a time, and then interchange two products. *)
(** Source for [exterior_generator_word]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma exterior_generator_word (v : V) (s : seq V) :
  wedge (exterior_generator v) (exterior_word s) =
    (-1 : K) ^+ size s *: wedge (exterior_word s) (exterior_generator v).
Proof.
elim: s => [|w s ih].
  by rewrite exterior_word_nil wedge_unitl wedge_unitr /= scale1r.
rewrite !exterior_word_cons wedge_assoc exterior_generator_skew -scaleN1r
  (bilZl wb) -wedge_assoc ih (bilZr wb) wedge_assoc scalerA.
by rewrite /= exprS.
Qed.

(** Source for [exterior_words_anticommutative]: Federer (1969), 1.3.1, p.
    13, polarisation identity and the concluding signed-interchange formula.
    In words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma exterior_words_anticommutative (s t : seq V) :
  wedge (exterior_word s) (exterior_word t) =
    (-1 : K) ^+ (size s * size t) *: wedge (exterior_word t) (exterior_word s).
Proof.
elim: s => [|v s ih].
  by rewrite exterior_word_nil wedge_unitl wedge_unitr /= scale1r.
rewrite !exterior_word_cons -wedge_assoc ih (bilZr wb) wedge_assoc
  exterior_generator_word (bilZl wb) -wedge_assoc scalerA.
by rewrite /= mulSn exprD mulrC.
Qed.

(** Federer 1.3.1, third paragraph: extend the preceding formula from
    spanning products to arbitrary homogeneous vectors. No restriction
    on the characteristic is needed for this conclusion. *)
(** Source for [exterior_anticommutative]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem exterior_anticommutative :
  graded_anticommutative (exterior_grading V) (@wedge K V).
Proof.
move=> m n x y hx hy; move: x hx.
apply: exterior_component_induction => [|x x' hx hx'|a x hx|s hs].
- by rewrite (bil0l wb) (bil0r wb) scaler0.
- by rewrite (bilDl wb) (bilDr wb) hx hx' scalerDr.
- by rewrite (bilZl wb) (bilZr wb) hx !scalerA mulrC.
move: y hy; apply: exterior_component_induction => [|y y' hy hy'|a y hy|t ht].
- by rewrite (bil0l wb) (bil0r wb) scaler0.
- by rewrite (bilDl wb) (bilDr wb) hy hy' scalerDr.
- by rewrite (bilZl wb) (bilZr wb) hy !scalerA mulrC.
by rewrite exterior_words_anticommutative hs ht.
Qed.
End Anticommutativity.
