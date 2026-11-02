(** Finite traces of binary cylinders, supporting the concrete
    counterexample in Federer (1969), 2.3.8, p. 78. Uniform counting on
    words of length n assigns a prefix w the fraction 2^(-size w). This will
    verify positivity of the covering measure without importing external
    measure theory. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import BinarySequenceCylinders BinaryWordRefinement
  CountingMeasure CountingFinitePredicate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_word_sequence]: extend a finite binary
    word by zero symbols, supporting finite traces in the local
    Federer 2.3.8 counterexample. *)
Definition binary_word_sequence (w : seq bool) : binary_sequence_space := nth false w.

(** Source for [binary_cylinder_finite_trace]: below the chosen
    finite-word length, membership in a cylinder is exactly the
    finite prefix condition; infrastructure for Federer 2.3.8,
    p. 78. *)
Lemma binary_cylinder_finite_trace n (u : n.-tuple bool) w : (size w <= n)%N ->
  (binary_cylinder w (binary_word_sequence u) <-> prefix w u).
Proof.
move=> hw; have hmin : minn (size w) n = size w by apply/minn_idPl.
split.
- move=> hx; rewrite prefixE; apply/eqP; apply: (@eq_from_nth _ false).
  + by rewrite size_take_min size_tuple hmin.
  + move=> k hk; rewrite nth_take; last by move: hk; rewrite size_take_min size_tuple hmin.
    apply: hx; by move: hk; rewrite size_take_min size_tuple hmin.
- move=> /prefixP [v he] k hk.
  by rewrite /binary_word_sequence he nth_cat hk.
Qed.

(** Source for [binary_cylinder_trace_count]: exact finite count
    of a cylinder trace, supporting the probability costs in the
    local example for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_trace_count (R : realType) n w (hw : (size w <= n)%N) :
  @counting_measure R [the finType of n.-tuple bool]
    [set u | binary_cylinder w (binary_word_sequence u)] = ((2 ^ (n-size w))%:R : R)%:E.
Proof.
have he : [set u : n.-tuple bool | binary_cylinder w (binary_word_sequence u)] =
    [set u : n.-tuple bool | prefix w u].
  apply/seteqP; split=> u.
  - exact: (proj1 (@binary_cylinder_finite_trace n u w hw)).
  - exact: (proj2 (@binary_cylinder_finite_trace n u w hw)).
have hc := congr1 (@counting_measure R [the finType of n.-tuple bool]) he.
apply: eq_trans hc _.
by rewrite counting_finite_predicate (binary_word_prefix_card hw).
Qed.
