(** General topology supporting Federer (1969), 2.2.10, p. 65: X times N is
    separable when X is. A product of two countable dense subsets is
    countable and dense in the maximum metric. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import MetricProductBackground SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_metric_product]: supporting separability
    assertion in Federer 2.2.10, p. 65, for two general
    separable metric factors. The dense set is the Cartesian
    product of given countable dense sets. *)
Theorem separable_metric_product (R : realType) (T U : metricType R) :
  (exists D : set T, countable D /\ dense D) ->
  (exists E : set U, countable E /\ dense E) ->
  exists H : set (metric_product T U), countable H /\ dense H.
Proof.
move=> [D [hD hd]] [E [hE he]]; exists (D `*` E); split.
- exact: countableX hD hE.
- move=> W [x hx] ho.
  have hn : nbhs x W by rewrite openE in ho; exact: ho x hx.
  have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hn.
  have [a [ha hax]] := metric_dense_point_near hd x.1 hr.
  have [b [hb' hbx]] := metric_dense_point_near he x.2 hr.
  exists (a,b); split; last by split.
  apply: hb; change (Order.max (mdist x.1 a) (mdist x.2 b) < r).
  by rewrite gt_max hax hbx.
Qed.
