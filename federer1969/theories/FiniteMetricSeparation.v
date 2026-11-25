(** Finite distinct points are separated by sufficiently small partition
    cells, supporting Federer (1969), 2.10.10, p. 176: the characteristic
    sums tend to the number of points in the fibre. This is elementary
    metric and finite-set infrastructure, not a separate book theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [finite_metric_points_separated]: a positive
    lower bound on distances between distinct members of a
    finite set, supporting the limit argument in Federer
    2.10.10, p. 176. Empty and singleton
    sets are allowed; no least positive distance is asserted
    for an arbitrary infinite set. *)
Lemma finite_metric_points_separated (R : realType) (X : metricType R) (B : {fset X}) :
  exists e : R, 0<e /\ forall x y, x \in B -> y \in B -> x!=y -> e<=mdist x y.
Proof.
pose d (p : (B*B)%type) : R := if val p.1==val p.2 then 1 else mdist (val p.1) (val p.2).
pose e := \big[Order.min/1]_(p : (B*B)%type) d p.
have hp : 0<e.
  rewrite /e; apply: (big_ind (fun r : R => 0<r)); first exact: ltr01.
  - by move=> r s hr hs; rewrite lt_min hr hs.
  - move=> [x y] _; rewrite /d /=; case: ifP=> hxy; first exact: ltr01.
    by rewrite mdist_gt0 hxy.
exists e; split=> // x y hx hy hxy.
have h := bigmin_le (1:R) ([` hx], [` hy]) d.
by rewrite /d /= (negbTE hxy) in h.
Qed.
