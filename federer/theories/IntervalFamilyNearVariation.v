(** Federer (1969), 2.9.20, p. 166: the bound in (3) implies the same bound
    for sums of variations. First approximate the variation on each of
    finitely many cells, then concatenate the refined families without
    changing their total length. Only the proved partition laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  OrderedIntervalFamilyUP OrderedIntervalFamilyConcatenation RealPartitionIntervalFamilies
  FineVariationPartitionUP FineNearMaximalVariationPartitions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_interval_family_variation_sum]: direct variation sum in
    the first consequent implication of Federer 2.9.20(3), p. 166 The real
    finite part is used only with a proof of locally finite variation, so no
    infinite variation is subtracted. *)
Definition real_interval_family_variation_sum (R : realType) (g : R -> R)
    (s : seq (R * R)) : R :=
  \sum_(uv <- s) fine (curve_variation (g : R -> real_line_metric R) uv.1 uv.2).

(** Source for [ordered_interval_family_near_variation]: supporting finite
    refinement proving the first consequence of (3) in Federer 2.9.20, p.
    166 An eligible family has a refinement with identical total length
    whose increment sum approximates the sum of variations from below. All
    witnesses are obtained from the abstract partition approximation
    theorem. The empty-family case is included. *)
Theorem ordered_interval_family_near_variation (R : realType) (g : R -> R)
    (a b : R) (s : seq (R * R)) (e : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_ordered_real_interval_family a b s -> 0<e -> exists t : seq (R * R),
    is_ordered_real_interval_family a b t /\
    real_interval_family_length t=real_interval_family_length s /\
    real_interval_family_variation_sum g s-real_interval_family_increment_sum g t<e.
Proof.
move=> hg; elim: s a e=> [|[u v] s ih] a e hs he.
- exists [::]; split=> //; split=> //.
  by rewrite /real_interval_family_variation_sum /real_interval_family_increment_sum !big_nil subrr.
- have [hau [huv [hvb hs']]] := hs.
  have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
  have [t [ht [hlen hgap]]] := ih v (e/2) hs' he2.
  have hfin := @curve_variation_fin_num R [the metricType R of real_line_metric R] g hg u v (ltW huv).
  have [p [hp [hmesh hpGap]]] := @fine_near_maximal_variation_partition_exists R
    [the metricType R of real_line_metric R] g u v 1 (e/2) (ltW huv) hfin ltr01 he2.
  have [hsort [hn [hh hl]]] := hp.
  pose q := real_partition_interval_cells p.
  have hq : is_ordered_real_interval_family a v q.
    apply: ordered_real_interval_family_lower_bound hau _.
    apply: real_partition_cells_ordered hsort _ _; by rewrite ?hh ?hl.
  have hqLen : real_interval_family_length q=v-u.
    by rewrite /q (@real_partition_cells_length R p u hsort) hh hl.
  have hqInc : real_interval_family_increment_sum g q=
    chain_sum (g : R -> real_line_metric R) p.
    exact: real_partition_cells_increments hsort.
  exists (q++t); split.
  + exact: ordered_real_interval_family_cat (le_trans hau (ltW huv)) hvb hq ht.
  split.
  + rewrite real_interval_family_length_cat hqLen hlen.
    by rewrite /real_interval_family_length big_cons.
  + rewrite real_interval_family_increment_sum_cat hqInc
      /real_interval_family_variation_sum big_cons -/real_interval_family_variation_sum.
    change (fine (curve_variation (g : R -> real_line_metric R) u v)+
      real_interval_family_variation_sum g s-
      (chain_sum (g : R -> real_line_metric R) p+real_interval_family_increment_sum g t)<e).
    lra.
Qed.
