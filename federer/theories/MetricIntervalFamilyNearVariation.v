(** Federer (1969), 2.9.22, pp. 167–168: extend the finite-family variation
    refinement of 2.9.20, p. 166, to metric targets. The existing scalar
    interval-family laws and partition witness construction are reused. No
    relevant erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength MetricCurveAbsoluteContinuityUP
  OrderedIntervalFamilyUP OrderedIntervalFamilyConcatenation RealPartitionIntervalFamilies
  FineVariationPartitionUP FineNearMaximalVariationPartitions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.


(** Source for [metric_partition_cells_increments]: supporting metric
    extension in Federer 2.9.22, pp. 167–168, of the refinement step in
    2.9.20, p. 166 Removing zero-width partition cells preserves the exact
    metric chain sum, even for discontinuous curves. *)
Lemma metric_partition_cells_increments (R : realType) (Y : metricType R)
    (g : R -> Y) (s : seq R) : sorted <=%O s ->
  metric_interval_family_increment_sum g (real_partition_interval_cells s)=chain_sum g s.
Proof.
elim: s=> [|t [|u rest] ih] /= hs; try by rewrite /metric_interval_family_increment_sum big_nil.
have /andP[htu hs'] := hs.
case: ifP=> htu'.
- rewrite /metric_interval_family_increment_sum big_cons.
  change (mdist (g t) (g u)+metric_interval_family_increment_sum g
    (real_partition_interval_cells (u::rest))=mdist (g t) (g u)+chain_sum g (u::rest)).
  by rewrite (ih hs').
- change (metric_interval_family_increment_sum g (real_partition_interval_cells (u::rest))=
    mdist (g t) (g u)+chain_sum g (u::rest)).
  have htuE : t=u by apply/eqP; rewrite eq_le htu leNgt htu'.
  by rewrite (ih hs') htuE mdistxx add0r.
Qed.

(** Source for [metric_interval_family_increment_sum_cat]:
    supporting refinement additivity in Federer 2.9.22,
    pp. 167–168, extending 2.9.20, p. 166. Concatenated
    families have the sum of their metric costs, including empty ones. *)
Lemma metric_interval_family_increment_sum_cat (R : realType) (Y : metricType R)
    (g : R -> Y) (s t : seq (R * R)) :
  metric_interval_family_increment_sum g (s++t)=
    metric_interval_family_increment_sum g s+metric_interval_family_increment_sum g t.
Proof. by rewrite /metric_interval_family_increment_sum big_cat. Qed.

(** Source for [metric_interval_family_variation_sum]: supporting metric
    extension in Federer 2.9.22, pp. 167–168, of the first consequent
    implication in 2.9.20(3), p. 166 The finite variation representatives
    are summed only under the accompanying locally BV hypotheses. *)
Definition metric_interval_family_variation_sum (R : realType) (Y : metricType R) (g : R -> Y)
    (s : seq (R * R)) : R :=
  \sum_(uv <- s) fine (curve_variation g uv.1 uv.2).


(** Source for [metric_ordered_interval_family_near_variation]: supporting
    metric extension in Federer 2.9.22, pp. 167–168, of the first consequent
    implication in 2.9.20(3), p. 166 Approximate all cell variations by one
    ordered refinement with the same total length; only the previously
    proved abstract near-maximal partition laws are used. *)
Theorem metric_ordered_interval_family_near_variation (R : realType) (Y : metricType R) (g : R -> Y)
    (a b : R) (s : seq (R * R)) (e : R) :
  curve_locally_finite_variation g ->
  is_ordered_real_interval_family a b s -> 0<e -> exists t : seq (R * R),
    is_ordered_real_interval_family a b t /\
    real_interval_family_length t=real_interval_family_length s /\
    metric_interval_family_variation_sum g s-metric_interval_family_increment_sum g t<e.
Proof.
move=> hg; elim: s a e=> [|[u v] s ih] a e hs he.
- exists [::]; split=> //; split=> //.
  by rewrite /metric_interval_family_variation_sum /metric_interval_family_increment_sum !big_nil subrr.
- have [hau [huv [hvb hs']]] := hs.
  have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
  have [t [ht [hlen hgap]]] := ih v (e/2) hs' he2.
  have hfin := @curve_variation_fin_num R Y g hg u v (ltW huv).
  have [p [hp [hmesh hpGap]]] := @fine_near_maximal_variation_partition_exists R
    Y g u v 1 (e/2) (ltW huv) hfin ltr01 he2.
  have [hsort [hn [hh hl]]] := hp.
  pose q := real_partition_interval_cells p.
  have hq : is_ordered_real_interval_family a v q.
    apply: ordered_real_interval_family_lower_bound hau _.
    apply: real_partition_cells_ordered hsort _ _; by rewrite ?hh ?hl.
  have hqLen : real_interval_family_length q=v-u.
    by rewrite /q (@real_partition_cells_length R p u hsort) hh hl.
  have hqInc : metric_interval_family_increment_sum g q=
    chain_sum g p.
    exact: metric_partition_cells_increments hsort.
  exists (q++t); split.
  + exact: ordered_real_interval_family_cat (le_trans hau (ltW huv)) hvb hq ht.
  split.
  + rewrite real_interval_family_length_cat hqLen hlen.
    by rewrite /real_interval_family_length big_cons.
  + rewrite metric_interval_family_increment_sum_cat hqInc
      /metric_interval_family_variation_sum big_cons -/metric_interval_family_variation_sum.
    change (fine (curve_variation g u v)+
      metric_interval_family_variation_sum g s-
      (chain_sum g p+metric_interval_family_increment_sum g t)<e).
    lra.
Qed.
