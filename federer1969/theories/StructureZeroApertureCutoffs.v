(** Federer (1969), 3.3.8, p. 295: cofinal radial cutoffs
    and the original pointwise ordinary zero-aperture limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeDensityUP StructurePlaneGrowth StructureProjectionKernel ExtendedRealBounds
  ExtendedRealReciprocalBounds PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_aperture_at]: the ordinary zero-growth
    condition at the fixed cutoff 1/i in Federer 3.3.8, p. 295,
    expressed by all positive real cost thresholds. This independent
    predicate has no nullity or covering conclusion built into it. *)
Definition structure_zero_aperture_at (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (x:inner_metric_space (@euclidean_inner_productP R n)) (delta:R):Prop:=
  forall b:R,0<b ->exists t:R,0<t /\forall r s:R,0<r<delta ->0<s<t ->
    (structure_cone_cost hmn phi B (x,p) r s<=b%:E)%E.

(** Source for [structure_zero_growth_reciprocal_cutoff]: the
    union of the B_i covers the original B in Federer 3.3.8,
    p. 295. Ordinary zero growth at some positive cutoff gives
    the all-threshold condition at a cofinal reciprocal cutoff.
    No source measurability, finite mass or uniform pointwise
    modulus is assumed. *)
Theorem structure_zero_growth_reciprocal_cutoff (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (x:inner_metric_space (@euclidean_inner_productP R n)):
  structure_plane_zero_growth m phi B x (structure_projection_kernel hmn p) ->
  exists i:nat,structure_zero_aperture_at hmn phi B p x (((i.+1)%:R:R)^-1).
Proof.
move=>[delta [hDelta hLimit]].
have [i hCutoff]:=positive_reciprocal_nat_small hDelta.
exists i=>b hb.
have hBE:(0%E<b%:E)%E by rewrite lte_fin.
have [t [ht hTail]]:=hLimit.2 b%:E hBE.
exists t; split=>// r s /andP [hr hri] /andP [hs hst].
have hrDelta:0<r<delta by apply/andP; split=>//; exact:lt_trans hri hCutoff.
have hCost:(structure_cone_cost hmn phi B (x,p) r s<=
    structure_plane_radial_supremum m phi B x (structure_projection_kernel hmn p) delta s)%E.
  apply:extended_real_sup_upper; by exists r.
exact:le_trans hCost (ltW (hTail s hs hst)).
Qed.
