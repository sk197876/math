(** Federer (1969), 3.2.31, p. 269: reduction from a
    finite measurable rectifiable source to the compact charts
    of 3.2.18, p. 255. Their omitted source remainder has
    almost everywhere null fibres by the rough Chapter 2 estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts CompactImagePositiveFibreRectifiability
  CountablePositiveFibreRectifiability HausdorffMeasure HausdorffFibreCutoffs
  NullFibresProperSource EuclideanClosedBallCompact MeasureUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RectifiablePositiveFibres.
Variable R:realType.
Variables m n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [rectifiable_positive_fibre_locus_countably_rectifiable]:
    supporting general-source reduction in Federer 3.2.31, p. 269.
    Compact Lipschitz chart images cover W up to source-null
    mass. Their positive fibre loci have proved countable measure
    rectifiability; the omitted fibres add only a null target
    remainder. No source/ambient dimension comparison or target
    rectifiability premise is added. *)
Theorem rectifiable_positive_fibre_locus_countably_rectifiable (F:X->Y)
    (W:set X) L k mu:
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R X m.+1) m.+1 W ->
  measure_measurable (@hausdorff_measure R X m.+1) W ->
  is_metric_lipschitz_bound setT F L ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|0<hausdorff_fibre_mass F W k y].
Proof.
move=>hv hmu hDim hRect hMeas hF.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have [K [psi hCharts]]:=@federer_3_2_18 R m.+1 n 2%R W hRect hMeas hTwo.
pose C j:set X:=psi j @` K j.
have hC j:is_countably_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|0<hausdorff_fibre_mass F (C j) k y].
  have hChart:=(hCharts.1 j).1.
  exact (@compact_image_positive_fibre_locus_countably_rectifiable R m n v F (psi j)
    (K j) L 2%R k mu hv hmu hDim hF (rectifiable_chart_global_bound hChart)
    (rectifiable_chart_compact hChart)).
have hR:measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F (W `\` \bigcup_j C j) k y=0].
  apply:(@null_hausdorff_fibres_proper_source R X Y F L (W `\` \bigcup_j C j) k mu _ hF).
  - move=>a r hr; exact (@euclidean_closed_metric_ball_compact R n a r).
  - rewrite -hDim; exact hCharts.2.2.
exact (@countable_positive_fibre_locus_rectifiable R X Y (@hausdorff_measure R X k)
  (@hausdorff_measure R Y mu) (@hausdorff_measure_is_measure R X k)
  (@hausdorff_measure_is_measure R Y mu) F W C mu hC hR).
Qed.
End RectifiablePositiveFibres.
