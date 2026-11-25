(** Federer (1969), 3.2.16, pp. 252–253:
    elementary laws of the independently defined
    approximate tangent cone. Derive these from the
    ordinary tangent cones of 3.1.21, without choosing
    a construction of the intersection. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureRestriction PartialFunctionUP
  MetricDensities TangentConeUP TangentConeBasic MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ApproximateTangents.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X -> R.
Hypothesis hNX : is_real_norm NX.
Variable phi : set X -> \bar R.
Variable m : nat.
Variable a : X.
Local Notation M := (real_norm_metric_space hNX).

(** Source for [measure_approximate_tangent_ordinary]:
    the defining intersection and the inclusion
    Tan({f=g},a) contains Tan_m(phi,a), Federer
    3.2.16, pp. 252–253. The same inclusion
    holds for every permitted full-density subset. *)
Lemma measure_approximate_tangent_ordinary (S : set X) :
  partial_function_graph (@metric_density R M m (measure_restrict phi (~` S))) a 0%E ->
  measure_approximate_tangent_cone hNX phi m a `<=` norm_tangent_cone NX S a.
Proof. by move=> hS v hv; exact: hv S hS. Qed.

(** Source for [measure_approximate_tangent_nonnegative_scale]:
    the cone property of Tan_m(phi,a) in
    Federer 3.2.16, p. 252. Zero scaling
    is conditional on an existing member, so the
    possible empty cone is not excluded. *)
Lemma measure_approximate_tangent_nonnegative_scale (v : X) (s : R) :
  measure_approximate_tangent_cone hNX phi m a v -> 0<=s ->
  measure_approximate_tangent_cone hNX phi m a (s *: v).
Proof.
move=> hv hs S hS.
exact: (@norm_tangent_nonnegative_scale R X NX hNX S a v s (hv S hS) hs).
Qed.

(** Source for [measure_approximate_tangent_closed]:
    supporting closedness of the cone used in the
    compact-direction argument of Federer 3.2.16,
    p. 253. It is an arbitrary intersection
    of the closed tangent cones of 3.1.21. *)
Theorem measure_approximate_tangent_closed :
  @closed M (measure_approximate_tangent_cone hNX phi m a).
Proof.
pose D : set (set X) := [set S |
  partial_function_graph (@metric_density R M m (measure_restrict phi (~` S))) a 0%E].
change (@closed M (\bigcap_(S in D) norm_tangent_cone NX S a)).
apply: closed_bigI=> S hS; exact: (@norm_tangent_cone_closed R X NX hNX S a).
Qed.
End ApproximateTangents.
