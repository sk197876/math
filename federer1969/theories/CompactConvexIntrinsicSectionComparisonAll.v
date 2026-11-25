(** Empty-generator completion of the original section
    comparison in Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex EuclideanBlockCoordinates
  IntegralGeometricGauge IntegralGeometricGaugeEmpty CompactConvexIntrinsicSectionComparison EuclideanLebesgueDimensions
  MeasureUP MeasureIntegralUP MeasureConullZeroIntegral MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_intrinsic_section_comparison_all]: supporting
    all closed convex covering generators in the deduction
    on p. 280 of Federer 3.2.45. The proved
    original nonempty compact theorem handles each
    nonempty generator. An empty generator has the
    original zero section gauges, zero ordinary integral
    and zero source cost. Both empty coordinate blocks
    and every degree endpoint remain. *)
Theorem compact_convex_intrinsic_section_comparison_all (R : realType) m q k (hKQ : (k<=q)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  compact K -> is_inner_convex K ->
  exists a : R,
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
        @integral_geometric_gauge R q k hKQ 1 [set z | K (@euclidean_block_join R m q (y,z))])) a%:E /\
    a%:E<= @integral_geometric_gauge R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 K.
Proof.
move=> hCompact hConvex; case: (pselect (K !=set0))=> [hNonempty|hEmpty].
- exact: compact_convex_intrinsic_section_comparison hNonempty hCompact hConvex.
- have hK : K=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  exists 0%R; split.
  + apply: (@measure_almost_zero_integral R
      (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_lebesgue_measure R m)
      (euclidean_lebesgue_is_measure R m)).
    apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _
      (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R m)))=> y _.
    change (@integral_geometric_gauge R q k hKQ 1
      [set z | K (@euclidean_block_join R m q (y,z))]=0).
    rewrite hK; exact: integral_geometric_gauge_empty (lexx 1).
  + by rewrite hK (@integral_geometric_gauge_empty R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 (lexx 1)).
Qed.
