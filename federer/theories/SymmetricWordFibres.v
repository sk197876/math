(** Federer (1969), 1.10.6, p. 49: functions from the m argument positions
    to the n basis indices and their occurrence counts. Local correction:
    the displayed fibre condition must quantify j in {1,...,n}; the book
    prints {1,...,m}. The local May 1987 erratum has no entry for this page. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricAlgebra SymmetricGrading SymmetricMultiIndices
  SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords SymmetricUnitMultiIndices
  SymmetricMultiIndexAddition SymmetricFormIsomorphism GradedComponents SymmetricMonomialBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_exponent_word_degree]: Federer 1.10.6,
    p. 49, supporting counting identity: the total number of
    occurrences is the length of the word. *)
Lemma symmetric_exponent_word_degree n (s : seq 'I_n) :
  symmetric_multi_degree (symmetric_exponent_word_count s) = size s.
Proof.
elim: s=> [|i s ih].
- by rewrite symmetric_exponent_word_count_nil symmetric_multi_degree_zero.
- by rewrite symmetric_exponent_word_count_cons symmetric_multi_degree_add
    symmetric_multi_unit_degree ih add1n.
Qed.

(** Source for [symmetric_word_count_permutation]: Federer 1.10.6,
    p. 49, supporting regrouping: a word is a permutation of
    the ordered monomial word with exactly its occurrence counts. *)
Lemma symmetric_word_count_permutation n (s : seq 'I_n) :
  perm_eq s (symmetric_monomial_word idfun (symmetric_exponent_word_count s)).
Proof.
apply/allP=> i _; apply/eqP.
have h := congr1 (fun a : symmetric_multi_index n => a i)
  (symmetric_exponent_word_count_monomial (symmetric_exponent_word_count s)).
by rewrite /symmetric_exponent_word_count !ffunE in h.
Qed.

(** Source for [symmetric_word_occurrence_monomial]: Federer 1.10.6,
    p. 49, each basis word equals the monomial indexed by its
    occurrence counts. This follows from commutativity, without any basis
    or characteristic assumption. *)
Lemma symmetric_word_occurrence_monomial (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) (s : seq 'I_n) :
  symmetric_word [seq e i | i <- s] =
    symmetric_monomial e (symmetric_exponent_word_count s).
Proof.
rewrite /symmetric_monomial -(@symmetric_monomial_word_map 'I_n V n idfun
  (symmetric_exponent_word_count s) e).
apply: symmetric_word_permutation.
exact: perm_map (symmetric_word_count_permutation s).
Qed.

(** Source for [symmetric_function_occurrence_degree]: Federer 1.10.6,
    p. 49, a function on m positions gives an exponent tuple
    of total degree m. *)
Lemma symmetric_function_occurrence_degree n m (s : {ffun 'I_m -> 'I_n}) :
  symmetric_multi_degree (symmetric_exponent_word_count [seq s i | i <- enum 'I_m]) = m.
Proof. by rewrite symmetric_exponent_word_degree size_map size_enum_ord. Qed.

(** Source for [symmetric_function_occurrences]: Federer 1.10.6,
    p. 49, the finite map from functions on m positions to
    Xi(n,m) recording their fibre cardinalities. The coordinate index
    ranges over n, correcting the printed m in the fibre condition. *)
Definition symmetric_function_occurrences n m (s : {ffun 'I_m -> 'I_n}) : symmetric_indices n m :=
  symmetric_indices_bound (@Sub (symmetric_multi_index n) (fun a => symmetric_multi_degree a == m)
    (symmetric_degree_indices n m)
    (symmetric_exponent_word_count [seq s i | i <- enum 'I_m])
    (introT eqP (symmetric_function_occurrence_degree s))).

(** Source for [symmetric_function_occurrencesE]: Federer 1.10.6,
    p. 49, forgetting the redundant coordinate bounds recovers
    the occurrence count of each basis index. *)
Lemma symmetric_function_occurrencesE n m (s : {ffun 'I_m -> 'I_n}) :
  symmetric_indices_unbound (symmetric_function_occurrences s) =
    symmetric_exponent_word_count [seq s i | i <- enum 'I_m].
Proof.
apply/ffunP=> i.
by rewrite /symmetric_function_occurrences /symmetric_indices_unbound
  /symmetric_indices_bound /symmetric_indices_bound_function /= !ffunE.
Qed.

(** Source for [symmetric_function_word_component]: Federer 1.10.6,
    p. 49, the symmetric product selected by a function is
    the monomial with the corresponding finite exponent index. *)
Lemma symmetric_function_word_component (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) m (s : {ffun 'I_m -> 'I_n}) :
  symmetric_tuple_component [tuple e (s i) | i<m] =
    symmetric_finite_monomial e (symmetric_function_occurrences s).
Proof.
apply: val_inj.
change (component_val (symmetric_tuple_component [tuple e (s i) | i<m]) =
  component_val (symmetric_finite_monomial e (symmetric_function_occurrences s))).
rewrite symmetric_tuple_componentE /symmetric_finite_monomial symmetric_monomial_componentE.
change (symmetric_word [seq e (s i) | i <- enum 'I_m] =
  symmetric_monomial e (symmetric_indices_unbound (symmetric_function_occurrences s))).
rewrite symmetric_function_occurrencesE -symmetric_word_occurrence_monomial map_comp.
by [].
Qed.
