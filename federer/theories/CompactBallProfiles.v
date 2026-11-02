(** Federer (1969), 2.10.21, p. 183: the profiles of nonempty compact sets
    contained in a fixed closed ball. Their pointwise closure retains the
    Lipschitz, nonnegativity and radial lower bounds. Compact uniform
    control follows from the finite-net argument on p. 182. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic
  CompactSetDistanceProfile LipschitzUP LipschitzFunctionClosed LipschitzCompactConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_sets_in_ball]: direct F_(a,r)
    in 2.10.21, p. 183. Its members are
    nonempty compact sets contained in the closed ball. *)
Definition compact_sets_in_ball (R : realType) (X : metricType R) (a : X) (r : R) :
  set (compact_metric_set X) := [set C | val C `<=` metric_closed_ball a r].

(** Source for [compact_ball_profiles]: direct image
    Omega(F_(a,r)) in 2.10.21, p. 183,
    with the cartesian product topology on functions. *)
Definition compact_ball_profiles (R : realType) (X : metricType R) (a : X) (r : R) :
    set (prod_topology (fun _ : X => real_line_metric R)) :=
  [set f | exists C : compact_metric_set X, compact_sets_in_ball a r C /\
    f=compact_set_distance_profile C].

(** Source for [pointwise_real_lower_constraint_closed]: supporting
    preservation of the radial lower bound by closure
    in 2.10.21, p. 183. A coordinate lower
    half-line is closed in the product topology. *)
Lemma pointwise_real_lower_constraint_closed (R : realType) (X : choiceType) (x : X) (b : R) :
  closed [set f : prod_topology (fun _ : X => real_line_metric R) | b<=f x].
Proof.
apply: (@preimage_closed (prod_topology (fun _ : X => real_line_metric R))
  (real_line_metric R) (fun f => f x) [set y | b<=y]).
- move=> f hf; exact: proj_continuous.
- exact: closed_ge.
Qed.

(** Source for [compact_ball_profile_closure_laws]: supporting
    properties of f in the closure of Omega(F_(a,r))
    in 2.10.21, p. 183. In particular,
    f(x)>=distance(a,x)-r bounds its sublevel sets. *)
Theorem compact_ball_profile_closure_laws (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R)) :
  closure (compact_ball_profiles a r) f ->
  is_metric_lipschitz_bound setT f 1 /\
  (forall x, 0<=f x) /\ (forall x, mdist a x-r<=f x).
Proof.
move=> hf.
have hEs := @metric_lipschitz_functions_closed R X [the metricType R of real_line_metric R] 1 (@ler01 R).
have hinc : compact_ball_profiles a r `<=` metric_lipschitz_functions 1.
  move=> g [C [hC ->]]; exact: compact_set_distance_profile_lipschitz.
have hLip := hEs f (@closureS _ _ _ hinc f hf).
split; first exact hLip.
split=> x.
- have hb := @pointwise_real_lower_constraint_closed R X x 0.
  apply: hb; apply: (@closureS _ (compact_ball_profiles a r) [set g | 0<=g x] _ f hf).
  move=> g [C [hC ->]]; exact: metric_set_distance_nonnegative (compact_set_distance_profile_specification C) x.
- have hb := @pointwise_real_lower_constraint_closed R X x (mdist a x-r).
  apply: hb; apply: (@closureS _ (compact_ball_profiles a r) [set g | mdist a x-r<=g x] _ f hf).
  move=> g [C [hC ->]].
  apply: (@metric_set_distance_greatest R X (val C) (compact_set_distance_profile C)
    (compact_set_distance_profile_specification C) x (mdist a x-r))=> y hy.
  have hdist : mdist a y<=r := hC y hy.
  have ht := metric_triangle a y x; rewrite (metric_sym y x) in ht; lra.
Qed.

(** Source for [compact_ball_profile_closure_approximation]: supporting
    approximation of a closure profile uniformly on a
    compact set, as used twice on p. 183 in
    2.10.21. The approximating set remains in F_(a,r). *)
Theorem compact_ball_profile_closure_approximation (R : realType) (X : metricType R)
    (a : X) (r : R) (f : prod_topology (fun _ : X => real_line_metric R))
    (K : set X) (e : R) :
  closure (compact_ball_profiles a r) f -> compact K -> 0<e ->
  exists C : compact_metric_set X, compact_sets_in_ball a r C /\
    forall x, K x -> `|f x-compact_set_distance_profile C x|<e.
Proof.
move=> hf hK he.
have hLip := (compact_ball_profile_closure_laws hf).1.
have [U [hU hbound]] := lipschitz_compact_uniform_neighborhood hLip hK he.
have [g [[C [hC hg]] hUg]] := hf U hU.
exists C; split=> // x hx.
have hgl : is_metric_lipschitz_bound setT g 1 by rewrite hg; exact: compact_set_distance_profile_lipschitz.
have hh := hbound g hUg hgl x hx.
by rewrite hg in hh.
Qed.
