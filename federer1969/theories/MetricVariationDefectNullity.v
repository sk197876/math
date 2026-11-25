(** Federer (1969), 2.9.22, pp. 167–168: extend the variation conclusion of
    2.9.19 to normed targets. This module expands the metric part of the
    fine near-maximal-partition argument on p. 165; it is valid for every
    metric target, independently of reflexivity. The scalar proof remains
    unchanged. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureAlmostBasic MetricVariationDefect FineVariationPartitionUP
  FineNearMaximalVariationPartitions MetricVariationDefectPartitionBound SmallCoefficientMeasureBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


(** Source for [metric_variation_defect_local_null]: supporting extension in
    Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p. 165
    A fine partition with arbitrarily small variation gap proves nullity on
    every finite source segment, including a singleton. *)
Lemma metric_variation_defect_local_null (R : realType) (Y : metricType R)
    (g : R -> Y) (n : nat) (p q : R) :
  curve_locally_finite_variation g -> p<=q ->
  lebesgue_scalar_measure (metric_variation_defect_locus g n `&` `[p,q])=0%E.
Proof.
move=> hg hpq; have hm := lebesgue_scalar_is_measure R.
pose m := ((n.+1)%:R : R).
have hmp : 0<m by rewrite /m ltr0n.
have hr : 0<m^-1 by rewrite invr_gt0.
apply: (@finite_reference_small_coefficients_zero R
  (lebesgue_scalar_measure (metric_variation_defect_locus g n `&` `[p,q])) 1%E
  (measure_nonnegative hm _) lee01 (@ltry R 1%R)).
move=> e he; rewrite mule1.
have heM : 0<e/m by rewrite divr_gt0.
have hf := @curve_variation_fin_num R Y g hg p q hpq.
have [s [hs [hmesh hnear]]] := @fine_near_maximal_variation_partition_exists R
  Y g p q m^-1 (e/m) hpq hf hr heM.
have hcell (a b : R) : a<=b -> b-a<m^-1 ->
    (lebesgue_scalar_measure (metric_variation_defect_locus g n `&` `[a,b])<=
      (m*metric_variation_defect g a b)%:E)%E.
  move=> hab hwidth; exact (@metric_variation_defect_locus_cell_bound R Y g n a b hg hab hwidth).
have hb := @metric_variation_defect_fine_partition_bound R Y g (metric_variation_defect_locus g n)
  m m^-1 p q s hcell hs hmesh.
have hArc : arc_length g q-arc_length g p=fine (curve_variation g p q).
  by rewrite -(@arc_length_increment R Y g hg p q hpq).
rewrite hArc in hb.
have hcost : m*(fine (curve_variation g p q)-chain_sum g s)<e.
  by move: hnear; rewrite ltr_pdivlMr // mulrC.
apply: le_trans hb _; rewrite lee_fin; exact: ltW hcost.
Qed.


(** Source for [metric_variation_defect_locus_null]: supporting extension in
    Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p. 165
    Countably many integer segments cover the source line, so each defect
    locus is null without a global finite-variation hypothesis. *)
Theorem metric_variation_defect_locus_null (R : realType) (Y : metricType R)
    (g : R -> Y) (n : nat) :
  curve_locally_finite_variation g -> lebesgue_scalar_measure (metric_variation_defect_locus g n)=0%E.
Proof.
move=> hg; have hm := lebesgue_scalar_is_measure R.
pose F k := metric_variation_defect_locus g n `&` `[-((k.+1)%:R : R),(k.+1)%:R].
have hFn k : lebesgue_scalar_measure (F k)=0%E.
  apply: (@metric_variation_defect_local_null R Y g n (-((k.+1)%:R : R)) (k.+1)%:R hg).
  have hk : (0<((k.+1)%:R : R)) by rewrite ltr0n.
  lra.
have hUn : lebesgue_scalar_measure (\bigcup_k F k)=0%E.
  apply: (@measure_null_countable_union R (real_line_metric R) nat (@lebesgue_scalar_measure R)
    hm setT F (countableP _)).
  by move=> k _; exact: hFn.
apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R) hm _ _ _ hUn).
move=> x hx; pose k := Num.bound `|x|.
have hk : `|x|<k%:R := archi_boundP (normr_ge0 x).
have hsucc : (k%:R : R)<=(k.+1)%:R by rewrite ler_nat leqnSn.
have hxbound := le_trans (ltW hk) hsucc.
exists k=> //; split=> //.
by rewrite /= in_itv /= -ler_norml.
Qed.


(** Source for [metric_variation_defect_union_null]: supporting extension in
    Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p. 165
    The union of all positive-index metric defect loci is null; no
    measurability premise is imposed. *)
Lemma metric_variation_defect_union_null (R : realType) (Y : metricType R) (g : R -> Y) :
  curve_locally_finite_variation g ->
  lebesgue_scalar_measure (\bigcup_n metric_variation_defect_locus g n)=0%E.
Proof.
move=> hg; apply: (@measure_null_countable_union R (real_line_metric R) nat
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) setT _ (countableP _)).
by move=> n _; exact: metric_variation_defect_locus_null hg.
Qed.
