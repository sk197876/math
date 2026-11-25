(** Federer (1969), 2.2.9, p. 65: elementary interval facts supporting the
    real-line construction with countable complement. The narrow
    num_normedtype import supplies the standard real metric and order
    topology as background, not a parametrisation theorem. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology num_normedtype.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_open_interval]: supporting open-interval definition for
    the special case X=R in Federer 2.2.9, p. 65. *)
Definition real_open_interval (R : realType) (a b : R) : set (real_line_metric R) :=
  [set x | a < x /\ x < b].

(** Source for [real_open_interval_open]: elementary order-topology
    support for the interval tree in Federer 2.2.9, p. 65. *)
Lemma real_open_interval_open (R : realType) (a b : R) :
  open (real_open_interval a b).
Proof. apply: openI; [exact: open_gt | exact: open_lt]. Qed.

(** Source for [real_open_interval_nonempty]: supporting nonempty
    child condition in Federer 2.2.9, p. 65: the midpoint
    belongs to the interval whenever its endpoints are ordered. *)
Lemma real_open_interval_nonempty (R : realType) (a b : R) :
  a < b -> real_open_interval a b !=set0.
Proof. move=> hab; have [h1 h2] := midf_lt hab; exists ((a+b)/2); by split. Qed.

(** Source for [real_open_interval_closure_bounds]: supporting
    closure estimate for Federer 2.2.9, p. 65: every point
    in the closure of (a,b) lies between the two endpoints. Only
    this inclusion, not equality of the closed interval, is needed. *)
Lemma real_open_interval_closure_bounds (R : realType) (a b x : R) :
  closure (real_open_interval a b) x -> a <= x /\ x <= b.
Proof.
have hc : closed ([set y : real_line_metric R | a <= y] `&` [set y | y <= b]).
  apply: closedI; [exact: closed_ge | exact: closed_le].
have hs : real_open_interval a b `<=` [set y | a <= y] `&` [set y | y <= b].
  by move=> y [hay hyb]; split; exact: ltW.
move=> hx; apply: hc; exact: closureS hs x hx.
Qed.

(** Source for [real_open_interval_diameter_bound]: supporting
    diameter estimate in Federer 2.2.9, p. 65: distances
    between points in the interval closure are at most b-a. *)
Lemma real_open_interval_diameter_bound (R : realType) (a b x y : R) :
  closure (real_open_interval a b) x -> closure (real_open_interval a b) y ->
  mdist (x : real_line_metric R) (y : real_line_metric R) <= b-a.
Proof.
move=> hx hy; have [hax hxb] := real_open_interval_closure_bounds hx.
have [hay hyb] := real_open_interval_closure_bounds hy.
rewrite real_line_metric_distanceE ler_norml; apply/andP; split.
- rewrite lerNl opprB; exact: lerB hyb hax.
- exact: lerB hxb hay.
Qed.

(** Source for [real_open_intervals_ordered_disjoint]: supporting
    disjointness in Federer 2.2.9, p. 65: open intervals
    with ordered nonoverlapping interiors are disjoint, even when
    their closures share an endpoint. *)
Lemma real_open_intervals_ordered_disjoint (R : realType) (a b c d : R) :
  b <= c -> real_open_interval a b `&` real_open_interval c d = set0.
Proof.
move=> hbc; apply/seteqP; split; last by move=> x [].
move=> x [[_ hxb] [hcx _]].
by have := lt_trans hxb (le_lt_trans hbc hcx); rewrite ltxx.
Qed.
