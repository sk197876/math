(** Federer (1969), 3.1.4, p. 215: for almost every point
    of B, the exceptional prefix shifts Z have density zero. This
    combines precisely 3.1.3(4) and (5), with the corrected >= threshold. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBlockCoordinates EuclideanSliceTranslation
  EuclideanSliceApproximateContinuity EuclideanSliceDensity EuclideanSliceVariationSets
  EuclideanApproximateTranslation EuclideanZeroDensityUnion RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition ProductSections
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureSetDensity MeasureApproximateLimitUP
  CenteredBallRelations MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_almost_slice_variation_density_zero]:
    the null-complement exhaustion by C(i,j,p,q) asserted in
    Federer 3.1.4, p. 215, before choosing q. The two
    exceptional alternatives are combined by finite subadditivity. *)
Theorem euclidean_almost_slice_variation_density_zero (R : realType) k l
    (B : set (inner_metric_space (@euclidean_inner_productP R (k+l))))
    (g : inner_metric_space (@euclidean_inner_productP R (k+l)) -> R^o) (e : R) :
  measure_measurable (@euclidean_lebesgue_measure R (k+l)) B ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R (k+l))]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R (k+l))
    (partial_function_total g) -> 0<e ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R (k+l)) B [set a |
    partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
      (product_vertical_section (euclidean_slice_variation_exception B g e) a))
      (0 : inner_metric_space (@euclidean_inner_productP R k)) 0%E].
Proof.
move=> hB hg he.
pose X := inner_metric_space (@euclidean_inner_productP R (k+l)).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose Leb := @euclidean_lebesgue_measure R (k+l).
pose V := @centered_closed_ball_relation R [the metricType R of Z].
have hb := (measure_almost_everywhere_on_implication _ _ _).1
  (euclidean_almost_slice_complement_density_zero hB).
have hc := euclidean_almost_slice_approximate_continuity hg.
have hall := @measure_almost_everywhere_and R [the choiceType of X] Leb
  (euclidean_lebesgue_is_measure R (k+l)) _ _ hb hc.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (@measure_almost_everywhere_mono R [the choiceType of X] Leb
  (euclidean_lebesgue_is_measure R (k+l)) _ _ _ hall)=> a [ha [c [hc0 hlim]]] hBa.
have hbase := ha hBa.
have hca : g a=c := hc0.
rewrite -hca in hlim.
pose N := [set u : Z | ~B (euclidean_block_join (u,(euclidean_block_split a).2))].
have hn : partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k) V N)
    ((euclidean_block_split a).1+0) 0%E by rewrite addr0.
have hN := @euclidean_zero_density_translation R k (euclidean_block_split a).1 0 N hn.
pose W := [set y : real_line_metric R | `|g a-y|<e].
have hW : nbhs (g a : real_line_metric R) W.
  apply: (metricType_numDomainType.nbhs_mdistP (g a : real_line_metric R) W).2.
  by exists e.
have hvar := @hlim W hW.
have heq : ~` partial_function_preimage
    (partial_function_precompose (@euclidean_slice_translation R k l a) (partial_function_total g)) W=
    [set z : Z | e<=`|g (euclidean_slice_translation a z)-g a|].
  apply/seteqP; split=> z.
  - move=> hn0; rewrite /= leNgt; apply/negP=> hgood; apply: hn0.
    exists (g (euclidean_slice_translation a z)); split=> //.
    by rewrite /W /= distrC.
  - move=> hbad [y [hy hWy]].
    change (g (euclidean_slice_translation a z)=y) in hy.
    move: hWy; rewrite /W /= -hy distrC ltNge hbad; by [].
rewrite heq in hvar.
have hU := euclidean_zero_density_union hN hvar.
exact hU.
Qed.
