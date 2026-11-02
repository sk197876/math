(** Federer (1969), 2.3.2(8), p. 74: separated sets can be distinguished by
    a closed set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MeasurableSeparationUP MetricSetDistanceUP
  MetricSetDistanceSealed MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [metric_separated_closure_disjoint]: supporting closure
    separation in Federer 2.3.2(8), p. 74 Only the abstract infimum laws of
    distance to a nonempty set are used. *)
Lemma metric_separated_closure_disjoint (R : realType) (Y : metricType R)
    (A B : set Y) : metric_sets_positively_separated A B ->
  forall y, B y -> ~ closure A y.
Proof.
move=> [delta [hp hs]] y hy hc.
case: (pselect (A !=set0))=> [hn|he].
- pose d := @MetricSetDistance.value R Y A hn.
  have hd := @MetricSetDistance.laws R Y A hn.
  have hzero : d y = 0 := (proj2 (metric_set_distance_zero_closure hd y)) hc.
  have hl : delta <= d y.
    apply: (@metric_set_distance_greatest R Y A d hd)=> a ha.
    rewrite metric_sym; exact: hs a ha y hy.
  have hbad := lt_le_trans hp hl; by rewrite hzero ltxx in hbad.
- have hA : A = set0 by apply/seteqP; split=> a // ha; apply: he; exists a.
  by rewrite hA closure0 in hc.
Qed.
