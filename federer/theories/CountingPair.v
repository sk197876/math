(** Federer (1969), 3.2.13, p. 250: the
    square map has two positive-target inverse
    values. Compute the actual counting measure
    of two distinct points from its finite-cardinality
    law, without a multiplicity hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal.
From Federer Require Import CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [counting_measure_distinct_pair]: the two-point
    fibre cardinality used by the Gamma square
    substitution, Federer 3.2.13, p. 250,
    from counting measure in 2.1.2, p. 54. *)
Lemma counting_measure_distinct_pair (R:realType) (X:choiceType) (a b:X):
  a!=b ->@counting_measure R X ([set a] `|` [set b])=(2:R)%:E.
Proof.
move=>hab.
have hSet:([set a] `|` [set b])=[set` [fset a;b]].
  apply/seteqP; split=>x; rewrite /= in_fset2.
  - move=>[hx|hx]; by rewrite hx eqxx ?orbT.
  - move=>/orP[/eqP hx|/eqP hx]; [left|right]; exact hx.
by rewrite hSet counting_measure_finite cardfs2 hab.
Qed.
