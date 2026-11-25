(** Federer (1969), 2.9.22, pp. 167–168: extend the variation conclusion of
    2.9.19 to normed targets. This module expands the metric part of the
    fine near-maximal-partition argument on p. 165; it is valid for every
    metric target, independently of reflexivity. The scalar proof remains
    unchanged. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength LebesgueScalarMeasure
  MeasureUP MeasureBasic FineVariationPartitionUP FineVariationPartitionJoin
  MetricVariationDefect RealIntervalCoverBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


(** Source for [metric_variation_defect_fine_partition_bound]: supporting
    extension in Federer 2.9.22, pp. 167–168, of the partition argument in
    2.9.19, p. 165 The sum telescopes to the supplied coefficient m times
    the total arc-length increment minus the actual metric chain sum; no
    measurability of the defect set is needed. *)
Lemma metric_variation_defect_fine_partition_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (C : set (real_line_metric R)) (m d p q : R) (s : seq R) :
  (forall a b : R, a<=b -> b-a<d ->
    (lebesgue_scalar_measure (C `&` `[a,b])<=(m*metric_variation_defect g a b)%:E)%E) ->
  is_variation_partition p q s -> variation_partition_mesh_lt d s ->
  (lebesgue_scalar_measure (C `&` `[p,q])<=
    (m*(arc_length g q-arc_length g p-chain_sum g s))%:E)%E.
Proof.
move=> hcell hs hmesh.
have haux : forall t : seq R, t<>[::] -> sorted <=%O t -> variation_partition_mesh_lt d t ->
    (lebesgue_scalar_measure (C `&` `[head 0%R t,last 0%R t])<=
      (m*(arc_length g (last 0%R t)-arc_length g (head 0%R t)-chain_sum g t))%:E)%E.
  elim=> [//|a [|b rest] ih] hne hsort hm.
  - have hb := @measure_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
      (lebesgue_scalar_is_measure R) (C `&` `[a,a]) `[a,a] (fun x hx => hx.2).
    by move: hb; rewrite lebesgue_scalar_segment // subrr /= subrr subr0 mulr0.
  - have /andP [hab hrest] : (a<=b) && sorted <=%O (b::rest) := hsort.
    have /andP [hwidth hrestmesh] : (b-a<d) && variation_partition_mesh_lt d (b::rest) := hm.
    have htail := ih (ltac:(by [])) hrest hrestmesh.
    have hfirst := hcell a b hab hwidth.
    have hcover := @real_restricted_segment_split_le R (@lebesgue_scalar_measure R)
      C a b (last 0%R (b::rest)) (lebesgue_scalar_is_measure R).
    apply: le_trans hcover _; apply: le_trans (leeD hfirst htail) _.
    have heq : m*metric_variation_defect g a b+
        m*(arc_length g (last 0%R (b::rest))-arc_length g b-chain_sum g (b::rest))=
      m*(arc_length g (last 0%R (a::b::rest))-arc_length g a-chain_sum g (a::b::rest)).
      rewrite /metric_variation_defect /=; ring.
    by rewrite -EFinD heq.
have [_ [hn _]] := hs.
have hne : s<>[::] by move=> heq; rewrite heq in hn.
have hb := haux s hne hs.1 hmesh.
have [hh hl] := variation_partition_zero_endpoints hs.
by rewrite hh hl in hb.
Qed.
