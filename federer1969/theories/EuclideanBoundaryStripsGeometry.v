(** Federer (1969), 3.2.43, printed p. 278:
    the original exterior and interior strips are disjoint
    subsets of the same actual boundary tube. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricOpenThickening
  EuclideanExteriorStripBoundaryTube BoundaryComplementIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_interior_strip_boundary_tube]: direct
    second containment in Federer 3.2.43, p. 278. Apply
    the exterior-strip result to the original complement;
    Int(S) is the complement of its closure and the two
    actual boundaries are equal. No selected distance
    or original source measurability is required. *)
Lemma euclidean_interior_strip_boundary_tube (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (interior S `\` (~`metric_open_thickening (~`S) r)) `<=`
    metric_open_thickening (closure S `\` interior S) r.
Proof.
move=>x [hInterior hNotCore].
have hTube:metric_open_thickening (~`S) r x:=contrapT hNotCore.
have hNoClosure:~closure (~`S) x.
  have hEq:interior S=~`closure (~`S) by rewrite -interiorC setCK.
  by rewrite hEq in hInterior.
have hBound:=@euclidean_exterior_strip_boundary_tube R n (~`S) r x (conj hTube hNoClosure).
by rewrite topological_boundary_complement in hBound.
Qed.

(** Source for [euclidean_boundary_strips_disjoint]: direct
    disjointness assertion in the proof of Federer 3.2.43,
    p. 278. The exterior strip avoids closure S, whereas
    the interior strip is contained in Int S subset closure S. *)
Lemma euclidean_boundary_strips_disjoint (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R) x:
  (metric_open_thickening S r `\` closure S) x ->
  (interior S `\` (~`metric_open_thickening (~`S) r)) x ->False.
Proof.
move=>[_ hOutside] [hInterior _]; apply:hOutside.
exact:subset_closure (interior_subset hInterior).
Qed.
