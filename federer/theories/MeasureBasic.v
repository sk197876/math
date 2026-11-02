(** Federer (1969), 2.1.2, pp. 53-54: consequences of the covering
    inequality. editions: MeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_empty]: Federer 2.1.2, p. 53,
    sentence following the defining inequality; the empty covering
    family forces the empty set to have measure zero. *)
Lemma measure_empty (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : is_measure mu -> mu set0 = 0.
Proof.
move=> hm; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hc : (@set0 I) `<=` \bigcup_(B in (@set0 (set I))) B by move=> x [].
have h := @measure_countable_cover R I mu hm set0 set0 (@countable0 (set I)) hc.
by rewrite nonnegative_sum_empty in h.
Qed.

(** Source for [measure_mono]: Federer 2.1.2, p. 53, sentence following the
    defining inequality; inclusion implies comparison of measures. *)
Lemma measure_mono (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  A `<=` B -> mu A <= mu B.
Proof.
move=> hAB; have hc : A `<=` \bigcup_(C in [set B]) C.
  move=> x hx; exists B; first by []; exact: hAB.
have h := @measure_countable_cover R I mu hm A [set B] (countable1 B) hc.
by rewrite nonnegative_sum_singleton ?measure_nonnegative in h.
Qed.
