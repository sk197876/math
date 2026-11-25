(** Federer (1969), 2.2.10, p. 66: distance to the complement distinguishes
    a proper open set from its complement. These supporting consequences of
    the abstract infimum laws justify that step. Source context and
    nonempty-set convention: MetricSetDistanceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceBasic MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_set_distance_approximation]: supporting
    infimum approximation for Federer 2.2.10, p. 66:
    for every positive error, a point of the nonempty set has
    distance less than the infimum plus that error. *)
Lemma metric_set_distance_approximation (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x e :
  0 < e -> exists a, A a /\ mdist x a < d x+e.
Proof.
move=> he; apply: contrapT=> hn.
have hl : forall a, A a -> d x+e <= mdist x a.
  move=> a ha; rewrite leNgt; apply/negP=> hh; apply: hn; by exists a.
have hh := @metric_set_distance_greatest R T A d hd x (d x+e) hl.
have ht : d x < d x+e by rewrite ltrDl.
by have := lt_le_trans ht hh; rewrite ltxx.
Qed.

(** Source for [metric_set_distance_zero_closure]: supporting
    topological meaning of the distance in Federer 2.2.10,
    p. 66: its zero set is exactly the closure of A.
    This derives the fact from the abstract laws and metric balls. *)
Lemma metric_set_distance_zero_closure (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x :
  d x = 0 <-> closure A x.
Proof.
split.
- move=> hx U hU.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x U) hU.
  have [a [ha hea]] := metric_set_distance_approximation hd x he.
  exists a; split=> //; apply: hb; by move: hea; rewrite hx add0r.
- move=> hx; apply/eqP; rewrite eq_le (metric_set_distance_nonnegative hd x) andbT.
  apply: contrapT=> hnle.
  have hdpos : 0 < d x by rewrite ltNge; apply/negP.
  have hn : nbhs x [set a | mdist x a < d x].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
    by exists (d x).
  have [a [ha hax]] := hx _ hn.
  have hh := le_lt_trans (@metric_set_distance_lower R T A d hd x a ha) hax.
  by rewrite ltxx in hh.
Qed.

(** Source for [metric_set_distance_positive_outside_closed]: supporting
    denominator fact for Federer 2.2.10, p. 66: outside a closed set its
    distance is strictly positive. This justifies the reciprocal in the
    open-set representation *)
Lemma metric_set_distance_positive_outside_closed (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x :
  closed A -> ~ A x -> 0 < d x.
Proof.
move=> hA hx; rewrite lt_def (metric_set_distance_nonnegative hd x) andbT.
apply/negP=> /eqP he; apply: hx; apply: hA.
apply: (proj1 (metric_set_distance_zero_closure hd x)); exact he.
Qed.
