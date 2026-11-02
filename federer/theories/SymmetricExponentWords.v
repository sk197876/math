(** Federer (1969), 1.10.2, p. 45: repeated one-form factors indexed by
    their exponent tuples. Supporting finite-word counting identities. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricMonomials
  SymmetricUnitMultiIndices SymmetricMultiIndexAddition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_exponent_word_count]: Federer 1.10.2,
    p. 45, count the number of occurrences of each coordinate label
    in a finite product of one-forms. *)
Definition symmetric_exponent_word_count n (s : seq 'I_n) : symmetric_multi_index n :=
  [ffun i => count_mem i s].

(** Source for [symmetric_exponent_word_count_nil]: Federer
    1.10.2, p. 45, an empty product has the zero exponent tuple. *)
Lemma symmetric_exponent_word_count_nil n :
  symmetric_exponent_word_count ([::] : seq 'I_n) = symmetric_multi_zero n.
Proof. apply/ffunP=> i; by rewrite /symmetric_exponent_word_count /symmetric_multi_zero !ffunE. Qed.

(** Source for [symmetric_exponent_word_count_cons]: Federer
    1.10.2, p. 45, adjoining the i-th factor adds its unit exponent. *)
Lemma symmetric_exponent_word_count_cons n (i : 'I_n) s :
  symmetric_exponent_word_count (i::s) =
    symmetric_multi_add (symmetric_multi_unit i) (symmetric_exponent_word_count s).
Proof.
apply/ffunP=> j.
rewrite symmetric_multi_addE /symmetric_exponent_word_count /symmetric_multi_unit !ffunE /=.
by rewrite eq_sym.
Qed.

(** Source for [symmetric_exponent_word_count_monomial]: Federer
    1.10.2, p. 45, the word listing alpha_i copies of each
    coordinate i has exactly exponent tuple alpha. *)
Lemma symmetric_exponent_word_count_monomial n (a : symmetric_multi_index n) :
  symmetric_exponent_word_count (symmetric_monomial_word idfun a) = a.
Proof.
apply/ffunP=> i; rewrite /symmetric_exponent_word_count ffunE
  /symmetric_monomial_word count_flatten sumnE !big_map.
under eq_bigr do rewrite count_nseq.
rewrite (bigD1 i) //= eqxx mul1n.
have hz : (\sum_(j < n | j != i) (j == i) * a j)%N = 0%N.
  apply: big1=> j hj; by rewrite (negbTE hj) mul0n.
by rewrite hz addn0.
Qed.
