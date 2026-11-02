(** Federer (1969), 2.10.24, p. 188, final paragraph: proved weighted
    Borel-cover laws for the actual Gross and integral-geometric gauges of
    2.10.4(1) and 2.10.5(1), pp. 172–173. These instances discharge the
    abstract supporting hypothesis; they do not postulate it or redefine the
    costs. Source context and supporting scalar references:
    ProjectedVolumeWeightedCovers.v and IntegralGeometricWeightedCovers.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ProjectedVolumeGaugeUP ProjectedVolumeGauge
  IntegralGeometricGauge WeightedBorelCoverCostUP ProjectedVolumeWeightedCovers IntegralGeometricWeightedCovers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_weighted_borel_cost]: supporting
    actual Gross cost instance for 2.10.24, p. 188,
    from the projection supremum of 2.10.4(1), p. 172.
    No positive-degree restriction is needed for this
    cover law under the existing empty-product convention. *)
Theorem projected_volume_weighted_borel_cost (R : realType) (n m : nat) :
  (m<=n)%N -> has_weighted_borel_cover_bound (@projected_volume_gauge R n m).
Proof.
move=> hmn J S G u A hG hu hA hS hdom.
have hh := @projected_volume_gauge_weighted_cover R n m J S G u A 1%R hmn hG hu hA hS ltr01 hdom.
by rewrite mul1e in hh.
Qed.

(** Source for [integral_geometric_weighted_borel_cost]: supporting
    actual normalized integral-geometric cost instance for
    2.10.24, p. 188, from 2.10.5(1), pp. 172–173.
    All exponents at least one, including infinity, are
    retained in the proved cost law. *)
Theorem integral_geometric_weighted_borel_cost (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : \bar R) :
  1<=p -> has_weighted_borel_cover_bound (@integral_geometric_gauge R n m hmn p).
Proof.
move=> hp J S G u A hG hu hA hS hdom.
have hh := @integral_geometric_gauge_weighted_cover R n m hmn p J S G u A 1%R
  hp hG hu hA hS ler01 hdom.
by rewrite mul1e in hh.
Qed.
