(** Federer (1969), 3.3.9, pp. 295–296: original infinite
    upper cone growth supplies arbitrarily small large-cost cones. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeDensityUP StructurePlaneGrowth StructureProjectionKernel ExtendedRealBounds
  PositiveRadiusLimits PositiveRadiusLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_infinite_cone_cost_witness]: supporting the
    simultaneous small-radius/aperture upper limit in Federer 3.3.9,
    pp. 295–296. For every positive radial and aperture cutoff
    and every finite threshold an original cone has strictly larger
    normalized cost. The upper limit is not replaced by an ordinary
    infinite limit; no cost-attainment or measurable-source premise. *)
Theorem structure_infinite_cone_cost_witness (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (x:inner_metric_space (@euclidean_inner_productP R n)) (delta t b:R):
  structure_plane_infinite_growth m phi A x (structure_projection_kernel hmn p) ->
  0<delta ->0<t ->exists r s:R,0<r<delta /\0<s<t /\
    (b%:E<structure_cone_cost hmn phi A (x,p) r s)%E.
Proof.
move=>hGrowth hDelta ht.
case:(pselect (exists r s:R,0<r<delta /\0<s<t /\
    (b%:E<structure_cone_cost hmn phi A (x,p) r s)%E))=>hWitness; first exact:hWitness.
exfalso.
have hBound:(positive_radius_upper_limit
    (structure_plane_radial_supremum m phi A x (structure_projection_kernel hmn p) delta)<=b%:E)%E.
  apply:(positive_radius_upper_eventual_bound ht)=>s hs.
  apply:extended_real_sup_least=>v [r [hr ->]].
  change (structure_cone_cost hmn phi A (x,p) r s<=b%:E)%E.
  rewrite leNgt; apply/negP=>hLarge; apply:hWitness.
  exists r,s; by split=>//; split.
rewrite (hGrowth delta hDelta) in hBound.
by have:=lt_le_trans (@ltry R b) hBound; rewrite ltxx.
Qed.
