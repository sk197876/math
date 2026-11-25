(** Private existence proof supporting Federer (1969),
    3.2.14, p. 252. The closed Lipschitz relation is
    single valued by the metric separation law. Only
    its sealing module and the assumptions audit may
    import this implementation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz
  PartialLipschitzClosedRelation PartialLipschitzClosureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_lipschitz_graph_closure_exists]:
    proved existence of the graph extension supporting
    closure of rectifiable sets, Federer 3.2.14, p. 252.
    No value is filled outside the actual closed graph. *)
Theorem partial_lipschitz_graph_closure_exists (R : realType)
    (X Y : metricType R) (f : partial_function X Y) (L : R) :
  is_partial_metric_lipschitz_bound f L ->
  exists g, is_partial_lipschitz_graph_closure f g.
Proof.
move=> hf.
pose G := [set p : X * Y | partial_function_graph f p.1 p.2].
have hsingle x y z : closure G (x,y) -> closure G (x,z) -> y=z.
  move=> hy hz.
  have hh := @partial_lipschitz_graph_closure_bound R X Y f L hf (x,y) (x,z) hy hz.
  rewrite /= mdistxx mulr0 in hh.
  apply: mdist_positivity; apply/eqP; by rewrite eq_le hh mdist_ge0.
exists (@Build_partial_function X Y (fun x y => closure G (x,y)) hsingle).
by move=> x y.
Qed.
