(** Metric background supporting Federer (1969), 3.2.14,
    p. 252: subsets of bounded sets are bounded and
    taking closure preserves boundedness. Euclidean
    bounded domains have compact closures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric MetricDiameterUP MetricDiameter MetricDiameterClosure
  CoveringFamilyUP EuclideanBoundedClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_bounded_subset]: bounded source
    restriction supporting Federer 3.2.14(1), p. 251.
    No nonemptiness is required. *)
Lemma metric_bounded_subset (R : realType) (X : metricType R)
    (A B : set X) : A `<=` B -> metric_set_bounded B -> metric_set_bounded A.
Proof. move=> hAB hB; exact: le_lt_trans (extended_metric_diameter_mono hAB) hB. Qed.

(** Source for [metric_bounded_empty]: the empty
    parametrizing domain in Federer 3.2.14(1), p. 251. *)
Lemma metric_bounded_empty (R : realType) (X : metricType R) :
  metric_set_bounded (@set0 X).
Proof. by rewrite /metric_set_bounded extended_metric_diameter_empty ltry. Qed.

(** Source for [metric_bounded_closure]: closure keeps
    a bounded parametrizing domain bounded, supporting
    Federer 3.2.14, p. 252. *)
Lemma metric_bounded_closure (R : realType) (X : metricType R)
    (A : set X) : metric_set_bounded A -> metric_set_bounded (closure A).
Proof. by rewrite /metric_set_bounded extended_metric_diameter_closure. Qed.

(** Source for [euclidean_bounded_closure_compact]:
    compact source closure supporting the rectifiable
    closure observation of Federer 3.2.14, p. 252.
    Empty domains and dimension zero are included. *)
Lemma euclidean_bounded_closure_compact (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m))) :
  metric_set_bounded A -> compact (closure A).
Proof.
move=> hA; case: (pselect (A !=set0))=> [hne|he].
- have hd0 := metric_diameter_nonnegative (extended_metric_diameter_specification A).
  have hfin : extended_metric_diameter A \is a fin_num by rewrite (ge0_fin_numE hd0).
  pose d := fine (extended_metric_diameter A).
  have hd : (extended_metric_diameter A<=d%:E)%E by rewrite /d fineK.
  exact: (euclidean_bounded_set_closure_compact hne hd).
- have hzero : A=set0.
    apply/seteqP; split=> x; first by move=> hx; exfalso; apply: he; exists x.
    by move=> [].
  rewrite hzero closure0; exact: compact0.
Qed.
