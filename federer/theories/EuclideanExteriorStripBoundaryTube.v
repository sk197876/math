(** Federer (1969), 3.2.43, printed p. 278:
    the original exterior strip lies in the actual open
    tube of the original boundary. Nearest witnesses are
    local and require no convexity or boundedness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric InnerNearestUP
  WhitneyNearestCenters EuclideanNearestBoundary MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_strip_boundary_tube]: direct
    first containment in the proof of Federer 3.2.43,
    p. 278. An original tube centre proves the closure
    nonempty. A local actual nearest point is on its
    boundary and no farther than that original centre.
    All natural dimensions and empty strips are retained. *)
Lemma euclidean_exterior_strip_boundary_tube (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (metric_open_thickening S r `\` closure S) `<=`
    metric_open_thickening (closure S `\` interior S) r.
Proof.
move=>x [[b hb hNear] hOutside].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hNonempty:closure S !=set0 by exists b; exact:subset_closure hb.
have [a hNearest]:=whitney_nearest_point_exists (@closed_closure X S) hNonempty x.
have [ha hNotInterior]:=euclidean_nearest_outside_boundary hOutside hNearest.
have hNotSInterior:~interior S a.
  move=>hInterior; apply:hNotInterior.
  exact:(interiorS (@subset_closure X S)) a hInterior.
exists a; first by split.
change (is_true (mdist (a:X) x<r)).
rewrite metric_sym inner_metric_distanceE.
have hMinimal:=inner_nearest_minimal_law hNearest (subset_closure hb).
have hCentre:inner_norm (@euclidean_inner_productP R n) (x-b)<r.
  by rewrite -inner_metric_distanceE metric_sym.
exact:le_lt_trans hMinimal hCentre.
Qed.
