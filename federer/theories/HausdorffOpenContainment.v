(** General metric topology supporting Federer (1969), 2.10.32, p. 196,
    closedness of the volume lower bound on the compact-set class. An open
    set containing a compact K also contains all sufficiently close compact
    sets in Hausdorff distance. Use the already proved compact finite-power
    neighbourhood lemma with one coordinate, then the abstract nearest-point
    and Hausdorff-distance bounds. No auxiliary hyperspace topology is
    introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactCoordinateNeighbourhood MetricOpenThickening CompactSetDistanceProfile
  CompactProfileNearest CompactHausdorffMetric HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_open_thickening_subset]: supporting
    uniform open neighbourhood of a compact member
    of C in 2.10.32, p. 196. The
    compact set may be empty. This is general
    topology expanded through the one-coordinate
    case of the preceding project finite-power lemma. *)
Lemma compact_open_thickening_subset (R : realType) (X : metricType R)
    (K W : set X) : compact K -> open W -> K `<=` W ->
  exists r : R, 0<r /\ metric_open_thickening K r `<=` W.
Proof.
move=> hK hW hKW.
pose U : set ('I_1 -> X) := [set p | W (p ord0)].
have hU : open U.
  apply: (@open_comp [the topologicalType of ('I_1 -> X)] X (fun p=>p ord0) W _ hW).
  by move=> p _; exact: proj_continuous.
have hinside p : (forall i : 'I_1, K (p i)) -> U p.
  move=> hp; exact (hKW (p ord0) (hp ord0)).
have [r [hr hTube]] := @compact_finite_power_neighbourhood R [the finType of 'I_1] X K U hK hU hinside.
exists r; split=> // x hx.
exact (hTube (fun _ : 'I_1=>x) (fun _=>hx)).
Qed.

(** Source for [hausdorff_compact_containment_open]: supporting
    stability of compact containment in an open
    near-optimal volume cover in 2.10.32,
    p. 196. Compact sets retain their existing
    Hausdorff metric; no unproved equivalence with
    a separately constructed hyperspace is used. *)
Theorem hausdorff_compact_containment_open (R : realType) (X : metricType R)
    (W : set X) : open W ->
  open [set K : compact_hausdorff_space X | val K `<=` W].
Proof.
move=> hW; rewrite openE=> K hK.
have [r [hr hTube]] := compact_open_thickening_subset (set_valP K).1 hW hK.
have hV : nbhs K [set D : compact_hausdorff_space X | mdist K D<r].
  apply: (metricType_numDomainType.nbhs_mdistP K _).2; by exists r.
apply: (@filterS _ (nbhs K) _ _ _ _ hV)=> D hD x hx.
have h0 := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R X) K D.
have hb := (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) K D h0).1 (lexx _).
have hd := hb.2 x hx.
have [a [ha hxa]] := compact_profile_nearest_point K x.
apply: hTube; exists a=> //.
change (is_true (mdist a x<r)).
rewrite metric_sym hxa; apply: le_lt_trans hd _.
by rewrite -compact_hausdorff_distanceE.
Qed.
