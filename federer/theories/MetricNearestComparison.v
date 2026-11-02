(** Federer (1969), 2.4.12, p. 87: supporting Borel partitions for
    finite-image density. here nearest-point comparisons provide such
    approximation partitions. The topology proof below uses only metric
    balls and countable Borel closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import MetricClosedBalls TopologicalBorel BorelFamilyBasic MeasurableRealPairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_nearer_set_borel]: supporting Borel comparison for
    the approximation partitions in Federer 2.4.12, p. 87 Rational
    thresholds separate two unequal distances, reducing the comparison to
    countable unions of open balls and complements of closed balls. *)
Lemma metric_nearer_set_borel (R : realType) (Y : metricType R) (a b : Y) :
  borel_set [set x : Y | mdist x a <= mdist x b].
Proof.
pose C q := [set x : Y | mdist b x < (ratr q : R)] `&`
  (~` metric_closed_ball a (ratr q : R)).
have he : [set x : Y | mdist x a <= mdist x b] = ~` (\bigcup_(q in @setT rat) C q).
  apply/seteqP; split=> x.
  - move=> hx [q _ [hb ha]].
    have ha' : (ratr q : R) < mdist a x by rewrite ltNge; apply/negP.
    change (is_true (mdist b x < (ratr q : R))) in hb.
    rewrite (metric_sym b x) in hb; rewrite (metric_sym a x) in ha'.
    have hbad := lt_le_trans (lt_trans hb ha') hx; by rewrite ltxx in hbad.
  - move=> hn; rewrite /= leNgt; apply/negP=> hlt.
    have [q [hb ha]] := @real_rationals_order_dense R (mdist x b) (mdist x a) hlt.
    apply: hn; exists q=> //; split.
    + change (is_true (mdist b x < (ratr q : R))); by rewrite metric_sym.
    + move=> hle; change (is_true (mdist a x <= (ratr q : R))) in hle.
      rewrite metric_sym in hle; have hbad := lt_le_trans ha hle; by rewrite ltxx in hbad.
rewrite he; apply: borel_set_complement.
apply: borel_set_countable_union; first exact: countableP.
move=> q _.
apply: (borel_family_binary_intersection (borel_sets_family Y)).
- apply: open_borel_set; exact: metric_open_ball_open.
- apply: borel_set_complement; apply: closed_borel_set; exact: metric_closed_ball_closed.
Qed.
