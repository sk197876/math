(** Index transport for the original intrinsic-volume gauge
    used in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [integral_geometric_gauge_index_equality]: supporting
    coefficient reindexing in Federer 3.2.45, p. 279,
    for the original gauge of 2.10.4, p. 172.
    Equal natural degrees and their dimension guards
    determine the same already defined gauge. The
    proof uses only index equality and irrelevance
    of the Boolean dimension proof. *)
Lemma integral_geometric_gauge_index_equality (R : realType) n p q
    (hP : (p<=n)%N) (hQ : (q<=n)%N) t
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  p=q -> @integral_geometric_gauge R n p hP t S= @integral_geometric_gauge R n q hQ t S.
Proof. move=> hEqual; subst q; by rewrite (bool_irrelevance hP hQ). Qed.
