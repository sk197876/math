(** Federer (1969), 2.9.20, p. 166: sum the absolute increment bounds over
    disjoint interval interiors. This supporting lemma isolates finite
    additivity and null endpoints from the curve's analytic hypotheses.
    Source context: OrderedIntervalFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OrderedIntervalFamilyUP OrderedIntervalFamilyUnion
  MeasureUP StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_interval_family_increment_mass_bound]: supporting
    finite sum estimate in Federer 2.9.20, p. 166 If each increment is
    bounded by the interval mass of an atomless measure, its sum is bounded
    by the mass of the disjoint union of the open interiors. *)
Lemma real_interval_family_increment_mass_bound (R : realType) (g : R -> R)
    (nu : set R -> \bar R) (a b : R) (s : seq (R * R)) :
  is_measure nu -> (forall u v : R, measure_measurable nu `]u,v[) ->
  (forall x : R, nu [set x]=0) ->
  (forall u v : R, (a<=u)%R -> (u<=v)%R -> (v<=b)%R ->
    `|g v-g u|%:E<=nu `[u,v]) ->
  is_ordered_real_interval_family a b s ->
  (real_interval_family_increment_sum g s)%:E<=nu (real_interval_family_open_union s).
Proof.
move=> hm hI hz hinc hs.
rewrite (@real_interval_family_open_union_measure R nu a b s hm hI hs)
  /real_interval_family_increment_sum -sumEFin !big_seq.
apply: lee_sum=> uv huv; case: uv huv=> u v huv.
have [hau [huv' hvb]] := ordered_real_interval_family_cell_bounds hs huv.
rewrite -(@measure_segment_open_interval R nu u v hm (hz u) (hz v)).
exact: hinc u v hau (ltW huv') hvb.
Qed.
