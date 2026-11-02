(** Federer (1969), 2.10.28(2)–(3), p. 192: zero-cost parents may have empty
    child families. This supporting boundary case is permitted by the
    printed definition of special and by the corrected singleton-root
    hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  SpecialIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_cost_interval_empty_special]: supporting
    empty special family for a zero-cost parent
    in 2.10.28, pp. 191–192. Exact
    mass and the test bound are both zero. *)
Lemma zero_cost_interval_empty_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) :
  concave_interval_cost h (val J)=0 -> is_special_interval_family h J fset0.
Proof.
move=> hJ; constructor.
- by move=> S; rewrite in_fset0.
- by move=> S T; rewrite in_fset0.
- by rewrite big_seq_fset0.
- move=> T; rewrite big_mkcond big_seq_fset0 /=; exact (@concave_interval_cost_nonnegative R h hg (val T)).
Qed.

(** Source for [zero_cost_root_empty_limit_exists]: local
    regression witness for the full hypotheses of
    2.10.28(3), p. 192, including the
    corrected singleton H_0. All later levels
    and the limit may be empty when the
    initial interval has zero cost; a proof
    may not assume each zero-cost leaf meets A. *)
Theorem zero_cost_root_empty_limit_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) :
  concave_interval_cost h (val J)=0 -> exists H,
    is_special_interval_tree h H /\ H 0%N=[fset J] /\ is_special_interval_tree_limit H set0.
Proof.
move=> hJ; pose H (j : nat) := if j is 0%N then [fset J] else fset0.
have ht : is_special_interval_tree h H.
  constructor.
  - exists J; by [].
  - move=> [|j] S T /=; last by rewrite in_fset0.
    rewrite !in_fset1=> /eqP -> /eqP ->; by rewrite eqxx.
  - by move=> j S; rewrite /H in_fset0.
  - move=> [|j] S /=; last by rewrite in_fset0.
    rewrite in_fset1=> /eqP ->.
    have he : special_interval_restriction fset0 (val J)=fset0 by apply/fsetP=> U; rewrite /special_interval_restriction in_fset in_fset0.
    rewrite he; exact (@zero_cost_interval_empty_special R h hg J hJ).
  - move=> e he; exists 1%N; move=> j hj S.
    case: j hj=> [|j] hj; first by [].
    by rewrite /H in_fset0.
exists H; split=> //; split=> // x; split; first by [].
move=> hall; have [S [hS _]] := hall 1%N.
by rewrite /H in_fset0 in hS.
Qed.
