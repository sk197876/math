(** Supporting generator laws for Federer (1969), 2.10.7, pp. 174–175:
    ordered endpoint pairs describe open intervals of diameter at most b-a,
    with nonnegative raw increment cost for nondecreasing g. These laws
    support every size-cutoff approximation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP TopologicalBorel
  MetricDiameter MetricDiameterReal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_interval_index]: supporting
    endpoint-pair witness for each nonempty
    bounded open interval in Federer 2.10.7,
    p. 174. *)
Definition stieltjes_interval_index (R : realType) (a b : R) (hab : (a<b)%R) :
    stieltjes_open_intervals R :=
  @exist _ (fun q : R*R => q \in [set q : R*R | (q.1<q.2)%R]) (a,b) (mem_set hab).

(** Source for [stieltjes_interval_cost_nonnegative]:
    supporting sign of the raw generator cost
    in Federer 2.10.7, p. 174. *)
Lemma stieltjes_interval_cost_nonnegative (R : realType) (g : R -> R) :
  (forall a b, (a<=b)%R -> (g a<=g b)%R) ->
  forall j : stieltjes_open_intervals R, 0<=stieltjes_interval_cost g j.
Proof.
move=> hg j; rewrite /stieltjes_interval_cost lee_fin subr_ge0.
apply: hg; exact: ltW (set_valP j).
Qed.

(** Source for [stieltjes_interval_borel]: direct
    Borel generator property in Federer 2.10.7,
    p. 174, from openness of bounded intervals. *)
Lemma stieltjes_interval_borel (R : realType) (j : stieltjes_open_intervals R) :
  borel_set (stieltjes_interval_set j).
Proof. apply: open_borel_set; exact: interval_open. Qed.

(** Source for [stieltjes_interval_diameter_bound]:
    supporting diameter cutoff for the interval
    refinements in Federer 2.10.7, p. 174.
    The open interval is contained in its
    segment, whose diameter is b-a. *)
Lemma stieltjes_interval_diameter_bound (R : realType) (j : stieltjes_open_intervals R) :
  extended_metric_diameter (stieltjes_interval_set j)<=((val j).2-(val j).1)%R%:E.
Proof.
have hab : ((val j).1<(val j).2)%R := set_valP j.
have hsub : stieltjes_interval_set j `<=` `[(val j).1,(val j).2].
  move=> x; rewrite /stieltjes_interval_set /= !in_itv /= => /andP[ha hb].
  by rewrite (ltW ha) (ltW hb).
have hd := @extended_metric_diameter_mono R [the metricType R of real_line_metric R]
  (stieltjes_interval_set j) `[(val j).1,(val j).2] hsub.
by rewrite (@extended_metric_diameter_segment R (val j).1 (val j).2 (ltW hab)) in hd.
Qed.
