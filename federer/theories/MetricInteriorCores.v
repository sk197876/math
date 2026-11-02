(** Federer (1969), 2.2.16, pp. 71–72: points at distance at least 1/n from
    the complement of an open set. The universal metric inequality below
    expresses this condition without assigning a real distance to the empty
    set, so the whole-space open set has the whole space as every core. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricClosedBalls ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_interior_core]: direct distance-bound
    predicate in the definition of C_n(V), Federer 2.2.16,
    p. 71. Every point outside U must be at
    least r away. For nonempty complements this is precisely
    the usual lower bound on distance to the complement. *)
Definition metric_interior_core (R : realType) (X : metricType R)
    (U : set X) (r : R) : set X :=
  [set x | forall y, ~ U y -> r <= mdist x y].

(** Source for [metric_interior_core_closed]: supporting closedness
    in Federer 2.2.16, pp. 71–72. The complement
    of the core is the union of open radius-r balls
    centred outside U; U need not itself be open here. *)
Lemma metric_interior_core_closed (R : realType) (X : metricType R)
    (U : set X) (r : R) : closed (metric_interior_core U r).
Proof.
have he : metric_interior_core U r =
    ~` (\bigcup_(y in ~` U) [set x | mdist y x < r]).
  apply/seteqP; split.
  - move=> x hx [y hy hxy].
    have hh := hx y hy; rewrite metric_sym in hh.
    by move: hxy; rewrite /mkset ltNge hh.
  - move=> x hx y hy; rewrite leNgt; apply/negP=> hd.
    apply: hx; exists y=> //; by rewrite /= metric_sym.
rewrite he; apply: open_closedC; apply: bigcup_open=> y hy.
exact: metric_open_ball_open.
Qed.

(** Source for [metric_interior_core_inside]: supporting inclusion
    C_n(V) in V in Federer 2.2.16, p. 71.
    A positive separation from the complement excludes a point
    of that complement itself. *)
Lemma metric_interior_core_inside (R : realType) (X : metricType R)
    (U : set X) (r : R) : 0 < r -> metric_interior_core U r `<=` U.
Proof.
move=> hr x hx; case: (pselect (U x))=> hu; first exact hu.
exfalso; have hh := hx x hu; rewrite mdistxx in hh.
by move: hr; rewrite ltNge hh.
Qed.

(** Source for [open_set_covered_by_reciprocal_cores]: supporting
    countable core exhaustion in Federer 2.2.16, p. 71.
    A ball inside U gives a positive complement-distance bound,
    which exceeds 1/(n+1) for some n. Whole-space and
    empty open sets require no separate distance convention. *)
Lemma open_set_covered_by_reciprocal_cores (R : realType) (X : metricType R)
    (U : set X) : open U -> forall x, U x ->
  exists n, metric_interior_core U (((n.+1)%:R)^-1) x.
Proof.
move=> ho x hx.
have hnb : nbhs x U by rewrite openE in ho; exact: ho x hx.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x U) hnb.
have [n hn] := positive_reciprocal_nat_small he.
exists n=> y hy.
have hd : e <= mdist x y.
  rewrite leNgt; apply/negP=> hd; apply: hy; exact: hb y hd.
exact: le_trans (ltW hn) hd.
Qed.
