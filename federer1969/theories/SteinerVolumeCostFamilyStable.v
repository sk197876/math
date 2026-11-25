(** Steiner stability of C in Federer (1969), 2.10.32, pp. 196–197. Use the
    sealed symmetrisation from 2.10.30 and its proved preservation of
    nonempty sections, compactness, convexity and Euclidean volume. Combine
    these with the new top-degree exterior-cost contraction. The compact-set
    code is only a witness of membership in the existing Hausdorff carrier;
    no choice of a new global operation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex OrthonormalFamilies
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded CoveringFamilyUP EuclideanLebesgueDimensions
  SteinerStableFamilyUP SteinerVolumeCostFamilyUP SteinerSymmetrisationUP SteinerSymmetrisationLaws
  SteinerSymmetrisation UnitNormalGeometry SteinerCompact SteinerConvex SteinerVolume SteinerExteriorCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_volume_cost_family_stable]: direct
    implication S in C implies its Steiner
    symmetrisation lies in C in 2.10.32,
    pp. 196–197. This implication itself does
    not require the printed positive thresholds;
    their positivity is retained for the later
    numerical comparison. Nonempty null sections
    retain their support. *)
Theorem steiner_volume_cost_family_stable (R : realType) (n : nat) (lambda mu : R) :
  is_steiner_stable_family (@euclidean_inner_productP R n) (@steiner_volume_cost_family R n lambda mu).
Proof.
move=> S [hconv [hvol hcost]] u hu.
pose hB := @euclidean_inner_productP R n.
pose E := inner_metric_space hB.
pose H := compact_hausdorff_space E.
have hb : metric_set_bounded (val S) := compact_metric_diameter_finite S.
pose T : set E := steiner_symmetrisation hB hu hb.
have hs : is_steiner_symmetrisation hB u (val S) T := steiner_symmetrisation_specification hB hu hb.
have hTc : compact T := steiner_preserves_compactness hs (set_valP S).1.
have hTne : T !=set0.
  have [x hx] := (set_valP S).2.
  pose y := normal_foot hB u x.
  have hy : inner_coordinate hB u y=0 := normal_coordinate_foot hB hu x.
  have hsrc : normal_scalar_section u (val S) y !=set0.
    exists (inner_coordinate hB u x).
    by rewrite /normal_scalar_section /= /y normal_decomposition.
  have [t ht] := (steiner_projection_support hs hy).1 hsrc.
  exists (y+t*:u); exact ht.
pose D : H := exist _ T (mem_set (conj hTc hTne)).
exists D; split; last exact hs.
split; first exact (steiner_preserves_convexity hs hb hconv).
split.
- have he := steiner_preserves_euclidean_volume hs (set_valP S).1.
  change (is_true ((lambda%:E<=euclidean_lebesgue_measure n T)%E)).
  by rewrite -he.
- exact (le_trans (steiner_top_exterior_cost_bound hs (set_valP S).1 hconv) hcost).
Qed.
