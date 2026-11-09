(** Federer (1969), 3.3.19, p. 305: the common
    original angular-tail density supplies late radial
    directions near any prescribed local unit normal. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric PartialFunctionUP
  PlanarUnitCircleGeometry CircularDiscAngularTailDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [circular_disc_late_normal_approximation]:
    every common angular-tail point has arbitrarily late
    original eta_j(a) within any positive distance of any
    actual unit normal. This is the direction-uniform step
    of 3.3.19, p. 305; no uncountable exceptional-set
    union or independently selected radial value is used. *)
Theorem circular_disc_late_normal_approximation (R:realType)
    (eta:nat->partial_function (inner_metric_space (@euclidean_inner_productP R 2))
      (inner_metric_space (@euclidean_inner_productP R 2))) a:
  (forall v,closure (circular_disc_radial_tail eta a v)= @planar_unit_circle R) ->
  forall (u:inner_metric_space (@euclidean_inner_productP R 2)) (e:R) J,
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->0<e ->
  exists j v,(J<=j)%N /\partial_function_graph (eta j) a v /\
    inner_norm (@euclidean_inner_productP R 2) (u-v)<e.
Proof.
move=>hDense u e J hu he.
pose E:= inner_metric_space (@euclidean_inner_productP R 2).
have hClosure:closure (circular_disc_radial_tail eta a J) u by rewrite hDense.
have hNeighbour:nbhs u [set v:E|mdist u v<e].
  apply:(metricType_numDomainType.nbhs_mdistP u _).2.
  exists e=>//;by move=>v hv.
have [v [[j [hj hGraph]] hNear]]:= hClosure _ hNeighbour.
exists j,v;split;first exact:ltnW hj.
split=>//.
Qed.
