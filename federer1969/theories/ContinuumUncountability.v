(** Set-theoretic background for Federer (1969), 2.2.4, p. 62. Cantor's
    diagonal theorem makes the natural power set uncountable. Kelley,
    General Topology, Appendix Theorem 161, p. 276 (Dover 2017 reprint of
    1955), gives this argument. We prove the needed special case locally and
    transfer it to the sequence space. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import SequenceSpace SequenceContinuumCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [natural_power_set_uncountable]: supporting Cantor diagonal
    argument, Kelley Appendix Theorem 161, p. 276, for Federer 2.2.4, p. 62
    An injection of all natural subsets into naturals would contradict
    membership of its own diagonal subset. *)
Lemma natural_power_set_uncountable : ~ countable (@setT (set nat)).
Proof.
move=> /countable_injP[g hg].
pose D := [set n | exists A : set nat, g A = n /\ ~ A n].
have hn : ~ D (g D).
  move=> [A [he hnot]].
  have hAD : A = D by apply: hg he; rewrite inE.
  have hh : D (g D) by exists A; split.
  rewrite hAD in hnot; exact: hnot hh.
have hh : D (g D) by exists D; split.
exact: hn hh.
Qed.

(** Source for [positive_sequence_uncountable]: Supporting Federer 2.2.4, p.
    62.This follows from its proved equality with the natural power set. *)
Lemma positive_sequence_uncountable (R : realType) :
  ~ countable (@setT (positive_sequence_space R)).
Proof.
move=> hc; apply: natural_power_set_uncountable.
by rewrite -(eq_countable (positive_sequence_continuum_cardinality R)).
Qed.
