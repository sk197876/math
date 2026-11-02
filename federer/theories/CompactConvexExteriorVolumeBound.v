(** Compact convex case of Federer (1969), 2.10.32, pp. 196–197. Both the
    actual Lebesgue volume and the exterior-diameter cost of a compact set
    are finite. Choose their justified real finite parts as the two class
    thresholds and apply the proved compact-class comparison. Retaining zero
    thresholds and the zero-ball alternative avoids an additional
    positive-threshold limit argument, including in dimension zero. No
    inequality is assumed when proving finiteness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CompactSetDistanceProfile
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP ExteriorMeasureGauge
  CompactExteriorCostFinite SteinerVolumeCostFamilyUP SteinerVolumeCostComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_lebesgue_exterior_bound]: direct
    compact convex consequence of the class C
    argument in 2.10.32, pp. 196–197.
    Actual finite volume and cost may be zero;
    both are justified before using their finite
    parts as class thresholds. *)
Theorem compact_convex_lebesgue_exterior_bound (R : realType) (n : nat)
    (K : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_inner_convex (val K) ->
  (euclidean_lebesgue_measure n (val K)<=exterior_diameter_cost n (val K))%E.
Proof.
move=> hconv.
have hv0 := measure_nonnegative (euclidean_lebesgue_is_measure R n) (val K).
have hvfin := @euclidean_compact_finite R n (val K) (set_valP K).1.
have hvnum : euclidean_lebesgue_measure n (val K) \is a fin_num.
  by rewrite (ge0_fin_numE hv0).
have hc0 := exterior_diameter_cost_nonnegative n (val K).
have hcfin := @compact_exterior_diameter_cost_finite R n n K.
have hcnum : exterior_diameter_cost n (val K) \is a fin_num.
  by rewrite (ge0_fin_numE hc0).
pose lambda := fine (euclidean_lebesgue_measure n (val K)).
pose mu := fine (exterior_diameter_cost n (val K)).
have hvol : euclidean_lebesgue_measure n (val K)=lambda%:E by rewrite /lambda fineK.
have hcost : exterior_diameter_cost n (val K)=mu%:E by rewrite /mu fineK.
have hmu : 0<=mu by rewrite hcost lee_fin in hc0.
have hmember : @steiner_volume_cost_family R n lambda mu K.
  split=> //; split; [by rewrite hvol|by rewrite hcost].
have hne : @steiner_volume_cost_family R n lambda mu !=set0 by exists K.
have hh := @steiner_volume_cost_threshold_comparison R n lambda mu hmu hne.
by rewrite hvol hcost lee_fin.
Qed.
