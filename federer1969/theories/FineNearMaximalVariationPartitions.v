(** Federer (1969), 2.9.19, p. 165: the finite sequence can have arbitrarily
    small mesh while its length sum approximates total variation. First
    approximate the abstract variation supremum, then apply the proved
    finite refinement. Downstream arguments use only the partition laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal
  topology lra.
From Federer Require Import CurveVariationUP ExtendedRealBounds FineVariationPartitionUP
  FineVariationPartitionRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [fine_near_maximal_variation_partition_exists]: direct
    finite-partition choice in Federer 2.9.19, p. 165 For a finite variation
    on [a,b], choose a sum within e of the supremum and refine it without
    decreasing length. Finiteness only on this segment suffices for this
    supporting result, which works in any metric target and includes
    degenerate segments and repeated endpoints. *)
Theorem fine_near_maximal_variation_partition_exists (R : realType) (Y : metricType R)
    (g : R -> Y) (a b d e : R) : a<=b ->
  curve_variation g a b \is a fin_num -> 0<d -> 0<e -> exists s : seq R,
    is_fine_near_maximal_variation_partition g a b d e s.
Proof.
move=> hab hf hd he.
have hsup : extended_real_sup (variation_sums g a b)=(fine (curve_variation g a b))%:E.
  change (curve_variation g a b=(fine (curve_variation g a b))%:E).
  by rewrite fineK.
have [z [[s [hs hz]] hnear]] := @extended_sup_approximation R
  (variation_sums g a b) (fine (curve_variation g a b)) e hsup he.
rewrite hz lte_fin in hnear.
have [t [ht [hm hlen]]] := @fine_variation_partition_refinement R Y g a b d s hd hs.
exists t; split; first exact ht.
split; first exact hm.
lra.
Qed.
