(** Federer (1969), 3.3.10, p. 296: original plane alternatives
    have exact countable reciprocal radial-cutoff descriptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  StructurePlaneGrowth StructurePlaneCostOrder ExtendedRealReciprocalBounds
  MeasureUP PositiveRightOrderLimit PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_plane_zero_reciprocal_iff]: the countable
    description of S1 in Federer 3.3.10, p. 296, using 3.3.2,
    pp. 287–288. The ordinary zero limit is retained at one actual
    cofinal reciprocal radial cutoff. No finiteness hypothesis. *)
Theorem structure_plane_zero_reciprocal_iff (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):
  is_measure phi ->(structure_plane_zero_growth m phi A a V <->exists i:nat,
    positive_right_extended_order_limit
      (structure_plane_radial_supremum m phi A a V (((i.+1)%:R:R)^-1)) 0%E).
Proof.
move=>hPhi; split.
- move=>[delta [hDelta hLimit]].
  have [i hi]:=positive_reciprocal_nat_small hDelta.
  have hPositive:0<((i.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  exists i; exact:(@structure_plane_zero_smaller_cutoff R n k m phi A a V
    (((i.+1)%:R:R)^-1) delta hPhi hPositive (ltW hi) hLimit).
- move=>[i hLimit]; exists (((i.+1)%:R:R)^-1); split=>//.
  by rewrite invr_gt0 ltr0n.
Qed.

(** Source for [structure_plane_infinite_reciprocal_iff]: the
    countable description of S2 in Federer 3.3.10, p. 296,
    using 3.3.2, pp. 287–288. Every positive real radial cutoff
    contains a reciprocal cutoff; upper infinity is retained. *)
Theorem structure_plane_infinite_reciprocal_iff (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):
  structure_plane_infinite_growth m phi A a V <->forall i:nat,
    positive_radius_upper_limit
      (structure_plane_radial_supremum m phi A a V (((i.+1)%:R:R)^-1))=+oo%E.
Proof.
split.
- move=>hAll i; apply:hAll; by rewrite invr_gt0 ltr0n.
- move=>hAll delta hDelta.
  have [i hi]:=positive_reciprocal_nat_small hDelta.
  exact:(@structure_plane_infinite_larger_cutoff R n k m phi A a V
    (((i.+1)%:R:R)^-1) delta (ltW hi) (hAll i)).
Qed.
