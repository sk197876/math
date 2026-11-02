(** Supporting uniform evaluation control for Federer (1969), 2.10.5(2), p.
    173, and 3.2.36, p. 272. Nearby projections are uniformly close on a
    fixed compact source set. Joint evaluation continuity and a compact
    product tube prove the assertion in the actual relative Hom topology.
    This is general topological background for the convex-volume argument,
    not the asserted continuity of projected volume itself. The projection
    and topology Source context are recorded in EuclideanProjectionSpace.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  RealMetricBackground MetricPairDistance TopologicalProductMaps CompactProductTube MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_projection_evaluation_control]:
    supporting compact-set perturbation bound for
    Federer 2.10.5(2), p. 173, and 3.2.36,
    p. 272. The compact source may be empty
    and is not required to be convex. *)
Theorem compact_projection_evaluation_control (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (e : R) :
  compact K -> 0<e ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q x, V q -> K x -> mdist (euclidean_projection_linear p x :
      inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear q x)<e.
Proof.
move=> hK he.
pose P := euclidean_projection_space R n m.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose F (z : P*X) : real_line_metric R :=
  mdist (euclidean_projection_linear p z.2 : Y) (euclidean_projection_linear z.1 z.2).
have hleft : continuous (fun z : P*X => (euclidean_projection_linear p z.2 : Y)).
  move=> z; exact: continuous_comp (@second_projection_continuous P X z)
    (@euclidean_projection_continuous R n m p z.2).
have hpair : continuous (fun z : P*X =>
    ((euclidean_projection_linear p z.2 : Y),(euclidean_projection_linear z.1 z.2 : Y))).
  exact: (@topological_pair_continuous (P*X)%type Y Y _ _ hleft
    (@euclidean_projection_evaluation_continuous R n m)).
have hF : continuous F.
  move=> z; exact: continuous_comp (hpair z) (@metric_pair_distance_continuous R Y _).
have hW : @open (real_line_metric R) [set t | t<e] := @open_lt R e.
have hinside x : K x -> F (p,x)<e by move=> _; rewrite /F mdistxx.
have [V [r [hV [hp [hr hsub]]]]] :=
  @compact_parameter_image_neighbourhood R P X (real_line_metric R) F p K [set t | t<e]
    hF hK hW hinside.
exists V; split=> //; split=> // q x hq hx.
have htx : metric_open_thickening K r x := @metric_open_thickening_includes R X K r hr x hx.
exact: hsub q x hq htx.
Qed.
