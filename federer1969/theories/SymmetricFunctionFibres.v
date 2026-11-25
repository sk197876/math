(** Federer (1969), 1.10.6, p. 49: the displayed condition characterizing
    functions with prescribed fibre cardinalities. The coordinate index j
    must range from 1 to n, correcting the printed m. The local May 1987
    erratum has no entry for this page. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds
  SymmetricCoordinateDualBasis SymmetricDividedMonomials SymmetricExponentWords
  SymmetricWordFibres SymmetricWordFibreCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_function_fibre_size]: Federer 1.10.6,
    p. 49, the j-th occurrence coordinate is exactly the
    cardinality of the inverse image of j under the given function. *)
Lemma symmetric_function_fibre_size n m (s : {ffun 'I_m -> 'I_n}) (j : 'I_n) :
  symmetric_indices_unbound (symmetric_function_occurrences s) j =
    #|[pred i : 'I_m | s i == j]|.
Proof.
rewrite symmetric_function_occurrencesE /symmetric_exponent_word_count ffunE count_map
  cardE /enum_mem -enumT size_filter.
rewrite filter_predT; apply: eq_count=> i; by rewrite /= eq_sym.
Qed.

(** Source for [symmetric_prescribed_fibre_condition]: Federer 1.10.6,
    p. 49, the finite exponent index equals alpha precisely
    when every fibre has the specified size. The quantification is over
    n coordinate labels, rather than the printed m. *)
Lemma symmetric_prescribed_fibre_condition n m (s : {ffun 'I_m -> 'I_n})
    (a : symmetric_indices n m) :
  (symmetric_function_occurrences s == a) =
    [forall j : 'I_n, #|[pred i : 'I_m | s i == j]| == symmetric_indices_unbound a j].
Proof.
apply/eqP/forallP=> [<- j|h].
- by rewrite -symmetric_function_fibre_size eqxx.
- apply: symmetric_indices_unbound_injective; apply/ffunP=> j.
  rewrite symmetric_function_fibre_size; exact: eqP (h j).
Qed.

(** Source for [symmetric_prescribed_fibre_count]: Federer 1.10.6,
    p. 49, the printed count in its explicit fibre form:
    exactly m!/alpha! functions have the prescribed cardinality at every
    one of the n basis indices. *)
Theorem symmetric_prescribed_fibre_count (R : rcfType) n m
    (a : symmetric_indices n m) :
  #|[pred s : {ffun 'I_m -> 'I_n} |
    [forall j : 'I_n, #|[pred i : 'I_m | s i == j]| == symmetric_indices_unbound a j]]| =
    m`! %/ symmetric_multi_factorial (symmetric_indices_unbound a).
Proof.
rewrite -(symmetric_fibre_cardinality R a).
apply: eq_card=> s; exact: esym (symmetric_prescribed_fibre_condition s a).
Qed.
