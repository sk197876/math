(** Federer (1969), 2.9.19, p. 165: every variation-defect set C_m has
    scalar Lebesgue measure zero. No measurability of C_m is presupposed:
    the outer-measure bounds prove its nullity. Natural n denotes the
    printed positive m=n+1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureAlmostBasic RealVariationDefectUP FineVariationPartitionUP
  FineNearMaximalVariationPartitions VariationDefectPartitionBound SmallCoefficientMeasureBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_variation_defect_local_null]: direct estimate on C_m
    intersect [p,q] in Federer 2.9.19, p. 165 A fine partition with
    variation gap below e/m bounds the restricted length by e. Letting e
    tend to zero proves nullity, including p=q. The proof uses only the
    chosen partition laws, not the uniform-refinement implementation. *)
Lemma real_variation_defect_local_null (R : realType)
    (g : R -> real_line_metric R) (n : nat) (p q : R) :
  curve_locally_finite_variation g -> p<=q ->
  lebesgue_scalar_measure (real_variation_defect_locus g n `&` `[p,q])=0%E.
Proof.
move=> hg hpq; have hm := lebesgue_scalar_is_measure R.
pose m := ((n.+1)%:R : R).
have hmp : 0<m by rewrite /m ltr0n.
have hr : 0<m^-1 by rewrite invr_gt0.
apply: (@finite_reference_small_coefficients_zero R
  (lebesgue_scalar_measure (real_variation_defect_locus g n `&` `[p,q])) 1%E
  (measure_nonnegative hm _) lee01 (@ltry R 1%R)).
move=> e he; rewrite mule1.
have heM : 0<e/m by rewrite divr_gt0.
have hf := @curve_variation_fin_num R [the metricType R of real_line_metric R] g hg p q hpq.
have [s [hs [hmesh hnear]]] := @fine_near_maximal_variation_partition_exists R
  [the metricType R of real_line_metric R] g p q m^-1 (e/m) hpq hf hr heM.
have hcell (a b : R) : a<=b -> b-a<m^-1 ->
    (lebesgue_scalar_measure (real_variation_defect_locus g n `&` `[a,b])<=
      (m*real_variation_defect g a b)%:E)%E.
  move=> hab hwidth; exact (@real_variation_defect_locus_cell_bound R g n a b hg hab hwidth).
have hb := @variation_defect_fine_partition_bound R g (real_variation_defect_locus g n)
  m m^-1 p q s hcell hs hmesh.
have hArc : arc_length g q-arc_length g p=fine (curve_variation g p q).
  by rewrite -(@arc_length_increment R [the metricType R of real_line_metric R] g hg p q hpq).
rewrite hArc in hb.
have hcost : m*(fine (curve_variation g p q)-chain_sum g s)<e.
  by move: hnear; rewrite ltr_pdivlMr // mulrC.
apply: le_trans hb _; rewrite lee_fin; exact: ltW hcost.
Qed.

(** Source for [real_variation_defect_locus_null]: direct nullity of each
    C_m in Federer 2.9.19, p. 165 Cover the real line by countably many
    finite integer segments and use the preceding local estimates. No global
    finite-variation assumption is imposed on the curve. *)
Theorem real_variation_defect_locus_null (R : realType)
    (g : R -> real_line_metric R) (n : nat) :
  curve_locally_finite_variation g -> lebesgue_scalar_measure (real_variation_defect_locus g n)=0%E.
Proof.
move=> hg; have hm := lebesgue_scalar_is_measure R.
pose F k := real_variation_defect_locus g n `&` `[-((k.+1)%:R : R),(k.+1)%:R].
have hFn k : lebesgue_scalar_measure (F k)=0%E.
  apply: (@real_variation_defect_local_null R g n (-((k.+1)%:R : R)) (k.+1)%:R hg).
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

(** Source for [real_variation_defect_union_null]: direct
    countable-exception conclusion in Federer 2.9.19, p. 165 The union over
    all positive printed indices m=n+1 remains null, so points with s'>|g'|
    can be discarded. *)
Lemma real_variation_defect_union_null (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g ->
  lebesgue_scalar_measure (\bigcup_n real_variation_defect_locus g n)=0%E.
Proof.
move=> hg; apply: (@measure_null_countable_union R (real_line_metric R) nat
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) setT _ (countableP _)).
by move=> n _; exact: real_variation_defect_locus_null hg.
Qed.
