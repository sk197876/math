(** Hausdorff closedness of endpoint constraints supporting Federer (1969),
    2.10.32, p. 196. The continuous exterior endpoint norm is bounded on
    every tuple in a compact set. Such a condition is Hausdorff closed:
    transport a violating tuple to nearby compact sets by nearest points and
    continuity. The supporting theorem is stated for an arbitrary continuous
    product function and includes empty coordinate families. Nearest choices
    are local to the proof, without an exposed construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype.
From Federer Require Import RealMetricBackground CompactSetDistanceProfile CompactProfileNearest
  CompactHausdorffMetric HausdorffEndpointTransport ProductCoordinateConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_continuous_endpoint_bounds_closed]: supporting
    Hausdorff-closed exterior-diameter constraint in
    2.10.32, p. 196. F will be the
    actual paired exterior norm; no continuity
    or uniqueness of a global nearest-point map
    is postulated. *)
Theorem hausdorff_continuous_endpoint_bounds_closed (R : realType) (X : metricType R)
    (I : eqType) (F : (I -> X) -> real_line_metric R) (M : R) :
  continuous F ->
  closed [set K : compact_hausdorff_space X |
    forall a : I -> X, (forall i, val K (a i)) -> F a<=M].
Proof.
move=> hF.
pose H := compact_hausdorff_space X.
pose P : set H := [set K | forall a : I -> X, (forall i, val K (a i)) -> F a<=M].
have hopen : open (~` P).
  rewrite openE=> K hK.
  have [a [ha hfa]] : exists a : I -> X, (forall i, val K (a i)) /\ M<F a.
    case: (pselect (exists a : I -> X, (forall i, val K (a i)) /\ M<F a))=> [//|hno].
    exfalso; apply: hK=> a ha.
    case: (leP (F a) M)=> [//|hbad]; exfalso; apply: hno; by exists a.
  have hw (D : H) i := compact_profile_nearest_point D (a i).
  pose b (D : H) (i : I) : X := projT1 (cid (hw D i)).
  have hmem D i : val D (b D i) := (projT2 (cid (hw D i))).1.
  have hd i D : mdist (a i) (b D i)=compact_set_distance_profile D (a i) :=
    (projT2 (cid (hw D i))).2.
  have hbcvg : b @ nbhs K --> a.
    apply: (@product_coordinate_filter_convergence H I (fun _=>X) (nbhs K) b a (nbhs_filter K))=> i.
    exact (@hausdorff_nearest_endpoint_converges R X (a i) K (fun D=>b D i) (ha i) (hd i)).
  have hFcvg : (fun D : H=>F (b D)) @ nbhs K --> F a.
    move=> U hU; exact (hbcvg (F @^-1` U) (hF a U hU)).
  have hupper : open [set z : real_line_metric R | M<z] := @open_gt R M.
  rewrite openE in hupper.
  have hn : nbhs (F a) [set z : real_line_metric R | M<z] := hupper (F a) hfa.
  have hnear : nbhs K [set D : H | M<F (b D)] := hFcvg _ hn.
  apply: (@filterS H (nbhs K) _ _ _ _ hnear)=> D hD hgood.
  have hle := hgood (b D) (fun i=>hmem D i).
  have hh := lt_le_trans hD hle; by rewrite ltxx in hh.
have hh := open_closedC hopen; by rewrite setCK in hh.
Qed.
