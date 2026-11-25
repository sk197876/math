(** Federer (1969), 3.3.4, p. 289:
    the original B_j and C_j growth
    alternatives and their exact countable
    reciprocal-radius descriptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP StructureCoordinateGrowth StructureCoordinateGrowthLaws
  ExtendedRealReciprocalBounds PositiveRadiusLimits PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Alternatives.
Variable R:realType.
Variables m k:nat.
Variable phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R.
Variable A:set (inner_metric_space (@euclidean_inner_productP R (m+k))).
Variable a:inner_metric_space (@euclidean_inner_productP R (m+k)).
Variable f:{linear R_n R (m+k)->R_n R (m+k)}.
Variable j:'I_k.

(** Source for [structure_coordinate_zero_growth]: the
    original B_j condition, Federer 3.3.4,
    p. 289: some positive radial cutoff
    gives an ordinary zero aperture limit
    of the original normalized coordinate costs. *)
Definition structure_coordinate_zero_growth:=
  exists delta:R,0<delta /\ positive_right_extended_order_limit
    (structure_coordinate_radial_supremum phi A a f j delta) 0%E.

(** Source for [structure_coordinate_infinite_growth]: the
    original C_j condition, Federer 3.3.4,
    p. 289: every positive radial cutoff
    gives infinite upper aperture growth. *)
Definition structure_coordinate_infinite_growth:=
  forall delta:R,0<delta ->positive_radius_upper_limit
    (structure_coordinate_radial_supremum phi A a f j delta)=+oo%E.

(** Source for [structure_coordinate_zero_reciprocal_iff]:
    the countable positive-radius description
    of B_j in Federer 3.3.4, p. 289,
    via the cofinality used in 3.3.2.
    The ordinary limit and all original
    positive apertures remain unchanged. *)
Theorem structure_coordinate_zero_reciprocal_iff:
  is_measure phi ->(structure_coordinate_zero_growth <->exists i:nat,
    positive_right_extended_order_limit
      (structure_coordinate_radial_supremum phi A a f j ((i.+1)%:R:R)^-1) 0%E).
Proof.
move=>hPhi; split.
- move=>[delta [hd hLimit]].
  have [i hi]:=positive_reciprocal_nat_small hd.
  have hPositive:0<((i.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  exists i; exact:(@structure_coordinate_zero_smaller_cutoff R m k phi A a f j
    ((i.+1)%:R:R)^-1 delta hPhi hPositive (ltW hi) hLimit).
- move=>[i hLimit]; exists ((i.+1)%:R:R)^-1; split=>//.
  by rewrite invr_gt0 ltr0n.
Qed.

(** Source for [structure_coordinate_infinite_reciprocal_iff]:
    the countable positive-radius description
    of C_j in Federer 3.3.4, p. 289.
    Every positive real cutoff contains a
    reciprocal cutoff, and actual supremum
    monotonicity preserves its infinite upper limit. *)
Theorem structure_coordinate_infinite_reciprocal_iff:
  structure_coordinate_infinite_growth <->forall i:nat,
    positive_radius_upper_limit
      (structure_coordinate_radial_supremum phi A a f j ((i.+1)%:R:R)^-1)=+oo%E.
Proof.
split.
- move=>hAll i; apply:hAll; by rewrite invr_gt0 ltr0n.
- move=>hAll delta hd.
  have [i hi]:=positive_reciprocal_nat_small hd.
  exact:(@structure_coordinate_infinite_larger_cutoff R m k phi A a f j
    ((i.+1)%:R:R)^-1 delta (ltW hi) (hAll i)).
Qed.
End Alternatives.
