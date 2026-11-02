(** Federer (1969), 2.4.17, p. 90: continuity on Closure P. This supporting
    general-topology fact supplies closed neighborhoods inside any
    neighborhood of an extended real number, including infinity. It follows
    from the order topology of Federer 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CountableOrderIntervals OrderFamilyIntervalOpen ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_closed_neighborhood_refinement]: supporting
    regularity of the extended real line for the closure continuity
    assertion in Federer 2.4.17, p. 90 *)
Lemma extended_real_closed_neighborhood_refinement (R : realType)
    (x : extended_real_line R) (B : set (extended_real_line R)) :
  nbhs x B -> exists C, closed C /\ nbhs x C /\ C `<=` B.
Proof.
move=> hB; rewrite itv_nbhsE in hB; have [it [hoi hxi] hiB] := hB.
case: it hoi hxi hiB=> [[[] a|[]]] [[] b|[]] //= _ hxi hiB; rewrite interval.in_itv /= ?andbT in hxi.
- have /andP[hax hxb] := hxi.
  have [r [har hrx]] := @extended_rationals_order_dense R a x hax.
  have [s [hxs hsb]] := @extended_rationals_order_dense R x b hxb.
  exists ([set y | (ratr r : R)%:E <= y] `&` [set y | y <= (ratr s : R)%:E]); split.
  + apply: closedI; first exact: order_closed_upper_ray_closed.
    exact: order_closed_lower_ray_closed.
  split.
  + rewrite nbhsE; exists (order_family_interval (fun q : rat => (ratr q : R)%:E) (Some r,Some s)); first split.
    * exact: (@order_family_interval_open _ [the orderTopologicalType _ of order_topology (\bar R)] rat (fun q : rat => (ratr q : R)%:E) _).
    * by split.
    * move=> y [hry hys]; split; [exact: ltW hry | exact: ltW hys].
  + move=> y [hry hys]; apply: hiB; rewrite /= interval.in_itv /=; apply/andP; split.
    * exact: lt_le_trans har hry.
    * exact: le_lt_trans hys hsb.
- have [r [har hrx]] := @extended_rationals_order_dense R a x hxi.
  exists [set y | (ratr r : R)%:E <= y]; split; first exact: order_closed_upper_ray_closed.
  split.
  + rewrite nbhsE; exists (order_family_interval (fun q : rat => (ratr q : R)%:E) (Some r,None)); first split.
    * exact: (@order_family_interval_open _ [the orderTopologicalType _ of order_topology (\bar R)] rat (fun q : rat => (ratr q : R)%:E) _).
    * by split.
    * move=> y [hry _]; exact: ltW hry.
  + move=> y hry; apply: hiB; rewrite /= interval.in_itv /= andbT; exact: lt_le_trans har hry.
- have [s [hxs hsb]] := @extended_rationals_order_dense R x b hxi.
  exists [set y | y <= (ratr s : R)%:E]; split; first exact: order_closed_lower_ray_closed.
  split.
  + rewrite nbhsE; exists (order_family_interval (fun q : rat => (ratr q : R)%:E) (None,Some s)); first split.
    * exact: (@order_family_interval_open _ [the orderTopologicalType _ of order_topology (\bar R)] rat (fun q : rat => (ratr q : R)%:E) _).
    * by split.
    * move=> y [_ hys]; exact: ltW hys.
  + move=> y hys; apply: hiB; rewrite /= interval.in_itv /=; exact: le_lt_trans hys hsb.
- exists setT; split; first exact: closedT.
  split; first exact: filterT.
  move=> y hy; apply: hiB; by rewrite /= interval.in_itv.
Qed.
