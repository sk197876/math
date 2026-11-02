(** Federer (1969), 1.6.6, p. 27, second displayed volume identity. Moving
    from interleaved pairs to two consecutive blocks contributes
    (-1)^(n(n-1)/2). This supporting argument works in any anticommutative
    graded algebra and counts the interchanges explicitly. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra binomial.
From Federer Require Import AlgebraUP GradedAlgebra WordEvaluation TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Words.
Variable K : fieldType.
Variable A : algebra K.
Variable G : grading A.
Hypothesis hmul : graded_product G (alg_mul A).
Hypothesis hunit : homogeneous G 0 (alg_one A).
Hypothesis hanti : graded_anticommutative G (alg_mul A).
Variable X : choiceType.
Variable f : X -> A.
Hypothesis hf : forall x, homogeneous G 1 (f x).
Local Notation mul := (alg_mul A).

(** Source for [graded_word_homogeneous]: Federer 1.6.6,
    p. 27, block reordering in the volume identity. Supporting degree
    calculation for a word in degree-one factors. *)
Lemma graded_word_homogeneous s : homogeneous G (size s) (word_eval f s).
Proof.
elim: s => [|x s ih] /=; first exact: hunit.
have h := hmul (hf x) ih.
by rewrite add1n in h.
Qed.

(** Source for [graded_words_commute]: Federer 1.6.6,
    p. 27, block reordering in the volume identity. Interchanging
    two words produces the sign given by their length product. *)
Lemma graded_words_commute s t :
  mul (word_eval f s) (word_eval f t) =
  (-1 : K)^+(size s * size t) *: mul (word_eval f t) (word_eval f s).
Proof. exact: hanti (graded_word_homogeneous s) (graded_word_homogeneous t). Qed.

(** Source for [graded_word_double_cons]: Federer 1.6.6,
    p. 27, block reordering in the volume identity. Moving the first
    second-block factor past the tail of the first block. *)
Lemma graded_word_double_cons a b s t :
  mul (word_eval f (a::s)) (word_eval f (b::t)) =
  (-1 : K)^+(size s) *:
    mul (mul (f a) (f b)) (mul (word_eval f s) (word_eval f t)).
Proof.
have hs : mul (word_eval f s) (f b) =
    (-1 : K)^+(size s) *: mul (f b) (word_eval f s).
  have h := graded_words_commute s [:: b].
  by rewrite /= muln1 alg_unitr in h.
change (mul (mul (f a) (word_eval f s)) (mul (f b) (word_eval f t)) =
  (-1 : K)^+(size s) *:
    mul (mul (f a) (f b)) (mul (word_eval f s) (word_eval f t))).
rewrite -(@alg_assoc K A) (@alg_assoc K A (word_eval f s)) hs
  (bilZl (alg_bilinear A)) (bilZr (alg_bilinear A))
  -(@alg_assoc K A) (@alg_assoc K A).
by [].
Qed.

Variable I : choiceType.
Variables P Q : I -> X.

(** Source for [paired_word_block_sign]: Federer 1.6.6,
    p. 27, second displayed volume identity. Separating the two
    members of each pair into ordered blocks uses binomial(n,2)
    interchanges, equal to n(n-1)/2. *)
Theorem paired_word_block_sign s :
  mul (word_eval f [seq P i | i <- s]) (word_eval f [seq Q i | i <- s]) =
  (-1 : K)^+'C(size s,2) *:
    word_eval f (flatten [seq [:: P i; Q i] | i <- s]).
Proof.
elim: s => [|i s ih]; first by rewrite /= alg_unitl scale1r.
rewrite map_cons map_cons (graded_word_double_cons (P i) (Q i)) size_map ih
  (bilZr (alg_bilinear A)) scalerA -exprD.
rewrite /= (@alg_assoc K A) binS bin1 addnC.
by [].
Qed.

(** Source for [paired_word_interleaving_sign]: Federer
    1.6.6, p. 27, second displayed volume identity. The interleaved
    word equals the same sign times the two-block word. *)
Theorem paired_word_interleaving_sign s :
  word_eval f (flatten [seq [:: P i; Q i] | i <- s]) =
  (-1 : K)^+'C(size s,2) *:
    mul (word_eval f [seq P i | i <- s]) (word_eval f [seq Q i | i <- s]).
Proof. by rewrite paired_word_block_sign signrZK. Qed.

(** Source for [paired_word_sign_exponent]: Federer 1.6.6,
    p. 27, exponent n(n-1)/2. Identification of the interchange count
    with the printed arithmetic expression. *)
Lemma paired_word_sign_exponent n : 'C(n,2) = (n * (n-1) %/ 2)%N.
Proof. by rewrite bin2 -divn2 subn1. Qed.
End Words.
