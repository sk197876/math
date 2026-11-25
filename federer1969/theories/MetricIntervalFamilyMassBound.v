(** Federer (1969), 2.9.22, pp. 167–168: metric form of the partition-mass
    estimate in 2.9.20(1)=>(2), p. 166. This uses only finite additivity on
    disjoint interval interiors and null endpoints; it is independent of
    derivative existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OrderedIntervalFamilyUP OrderedIntervalFamilyUnion MetricCurveAbsoluteContinuityUP
  MeasureUP StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.


(** Source for [metric_interval_family_increment_mass_bound]: supporting
    metric sum estimate in Federer 2.9.22, pp. 167–168, extending the
    partition argument of 2.9.20, p. 166 Null endpoints replace closed
    masses by disjoint open interior masses before finite summation. *)
Lemma metric_interval_family_increment_mass_bound (R : realType) (Y : metricType R) (g : R -> Y)
    (nu : set R -> \bar R) (a b : R) (s : seq (R * R)) :
  is_measure nu -> (forall u v : R, measure_measurable nu `]u,v[) ->
  (forall x : R, nu [set x]=0) ->
  (forall u v : R, (a<=u)%R -> (u<=v)%R -> (v<=b)%R ->
    (mdist (g u) (g v))%:E<=nu `[u,v]) ->
  is_ordered_real_interval_family a b s ->
  (metric_interval_family_increment_sum g s)%:E<=nu (real_interval_family_open_union s).
Proof.
move=> hm hI hz hinc hs.
rewrite (@real_interval_family_open_union_measure R nu a b s hm hI hs)
  /metric_interval_family_increment_sum -sumEFin !big_seq.
apply: lee_sum=> uv huv; case: uv huv=> u v huv.
have [hau [huv' hvb]] := ordered_real_interval_family_cell_bounds hs huv.
rewrite -(@measure_segment_open_interval R nu u v hm (hz u) (hz v)).
exact: hinc u v hau (ltW huv') hvb.
Qed.
