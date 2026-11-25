(** Federer (1969), 3.2.32, pp. 269–270: supporting
    actual chart descriptions of the approximate differential.
    These are consequences of 3.2.18–19, not extra source data. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP MeasureUP MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  RectifiableCompactChartsUP RectifiableCompactCharts RectifiableChartDensityDifferential
  RectifiableDifferentialChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_differential_chart_supply_almost]: supporting
    the rank conclusion of Federer 3.2.32, p. 269, by the
    actual chart-chain rule in 3.2.19, p. 256. Almost every
    source point has an injective source-chart differential and
    an actual composite differential with the exact partial graph.
    Charts and differentials are only local existential witnesses. *)
Theorem rectifiable_differential_chart_supply_almost (R:realType) m n v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
      exists (K:set (R_n R m)) (psi:R_n R m->R_n R n),
        is_rectifiable_differential_chart_point W K psi F w].
Proof.
move=>hRect hW hF.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have [K [psi hCover]]:=@federer_3_2_18 R m n 2%R W hRect hW hTwo.
pose P:=fun i=>psi i @` K i.
pose Q:=fun i=>[set w|P i w ->is_rectifiable_differential_chart_point W (K i) (psi i) F w].
have hEach i:measure_almost_everywhere H (Q i).
  have hRaw:=rectifiable_chart_density_differential hTwo (hCover.1 i).1 (hCover.1 i).2
    hW hRect.2 hF.
  apply:(measure_almost_everywhere_mono hH _
    ((measure_almost_everywhere_on_implication _ _ _).1 hRaw))=>w hw hPi.
  exact:(hw hPi).2.
have hAll:=measure_almost_everywhere_countable hH (countableP (@setT nat)) (fun i _=>hEach i).
have hCovered:measure_almost_everywhere H [set w|W w ->(\bigcup_i P i) w].
  exact:(measure_almost_everywhere_on_implication _ _ _).1 hCover.2.2.
have hBoth:=measure_almost_everywhere_and hH hAll hCovered.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hBoth)=>w [hEvery hIn] hw.
have [i _ hPi]:=hIn hw; exists (K i),(psi i); exact:(hEvery i Logic.I hPi).
Qed.
