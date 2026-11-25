(** Federer (1969), 2.10.21, p. 183, first paragraph: if Y is boundedly
    compact, the Lipschitz functions with fixed bound and a bounded value at
    one point form a compact set in the cartesian product topology. Follow
    the printed compact-ball product argument using general topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import LipschitzUP MetricClosedBalls LipschitzFunctionClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_boundedly_compact]: boundedly compact
    hypothesis in 2.10.21, p. 183, expressed
    by compactness of every closed ball of finite
    nonnegative radius. This predicate specifies a
    property of the given metric space. *)
Definition metric_boundedly_compact (R : realType) (Y : metricType R) :=
  forall (b : Y) (r : R), 0<=r -> compact (metric_closed_ball b r).

(** Source for [anchored_lipschitz_functions]: direct
    bounded-value subset of E_s in 2.10.21,
    p. 183. The domain may otherwise be arbitrary. *)
Definition anchored_lipschitz_functions (R : realType) (X Y : metricType R)
    (s : R) (a : X) (b : Y) (r : R) : set (prod_topology (fun _ : X => Y)) :=
  metric_lipschitz_functions s `&` [set f | mdist (f a) b<=r].

(** Source for [anchored_lipschitz_functions_compact]: direct
    compactness assertion of 2.10.21, p. 183.
    Each coordinate lies in the compact ball of
    radius r+s distance(a,x) about b. No countability
    or separability of the domain is assumed. *)
Theorem anchored_lipschitz_functions_compact (R : realType) (X Y : metricType R)
    (s : R) (a : X) (b : Y) (r : R) :
  metric_boundedly_compact Y -> 0<=s -> 0<=r ->
  compact (@anchored_lipschitz_functions R X Y s a b r).
Proof.
move=> hY hs hr.
have ha : closed [set f : prod_topology (fun _ : X => Y) | mdist (f a) b<=r].
  apply: continuous_metric_distance_constraint_closed.
  - exact: proj_continuous.
  - exact: cst_continuous.
have hc := closedI (@metric_lipschitz_functions_closed R X Y s hs) ha.
have hrad x : 0<=r+s*mdist a x by rewrite addr_ge0 // mulr_ge0 // mdist_ge0.
have hball x : compact (metric_closed_ball b (r+s*mdist a x)) := hY b _ (hrad x).
have hbox := @tychonoff X (fun _ : X => Y) (fun x => metric_closed_ball b (r+s*mdist a x)) hball.
apply: (subclosed_compact hc hbox)=> f [[h0 hf] hfa] x.
apply: le_trans (metric_triangle b (f a) (f x)) _.
rewrite (metric_sym b (f a)); exact: lerD hfa (hf a x I I).
Qed.
