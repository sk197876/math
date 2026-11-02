(** Topological endpoint transport supporting Federer (1969), 2.10.32, p.
    196, the claim that the compact convex class with a fixed
    exterior-diameter bound is Hausdorff closed. A nearest point to a fixed
    member of K in each nearby compact D converges to that fixed point. The
    theorem quantifies over any selection satisfying the nearest-point
    distance law; it neither exposes a particular selection construction nor
    assumes a globally continuous nearest-point operation. This is general
    metric topology supporting the printed closedness claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactProfileNearest
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_nearest_endpoint_converges]: supporting
    endpoint approximation in the Hausdorff-closedness
    claim in 2.10.32, p. 196. The fixed
    point need only belong to K; uniqueness of
    nearest points and continuity away from K are
    not assumed. *)
Lemma hausdorff_nearest_endpoint_converges (R : realType) (X : metricType R)
    (a : X) (K : compact_hausdorff_space X) (p : compact_hausdorff_space X -> X) :
  val K a -> (forall D, mdist a (p D)=compact_set_distance_profile D a) ->
  p @ nbhs K --> a.
Proof.
move=> ha hp U hU.
have [e he hb] := (metricType_numDomainType.nbhs_mdistP a U).1 hU.
have hV : nbhs K [set D : compact_hausdorff_space X | mdist K D<e].
  apply: (metricType_numDomainType.nbhs_mdistP K _).2; by exists e.
apply: (@filterS _ (nbhs K) _ _ _ _ hV)=> D hD; apply: hb.
have hnon := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R X) K D.
have hh := (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) K D hnon).1 (lexx _).
have hbound := hh.1 a ha.
change (is_true (mdist a (p D)<e)).
rewrite hp; apply: le_lt_trans hbound _.
by rewrite -compact_hausdorff_distanceE.
Qed.
