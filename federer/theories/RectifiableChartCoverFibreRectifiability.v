(** Federer (1969), 3.2.22(2), p. 258: assemble
    the strict-dimension coordinate fibres across the countable
    source/target chart pairs, retaining the null omitted fibres. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  MetricLipschitzComposition RectifiableSetUP RectifiableCompactChartsUP RectifiableChartPairPieces
  RectifiableChartInverseExtension LipschitzPairFibreRectifiability RectifiableChartPairOmittedFibres
  CountablyMeasureRectifiableOperations CountablyMeasureRectifiableNullRemainder MappingFibreSetAlgebra
  HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_chart_cover_fibres_countably_rectifiable]:
    supporting strict-dimension fibre conclusion of Federer
    3.2.22(2), p. 258. A countable common
    conull target set handles every chart pair. Unite
    their actual countable rectifiable covers, then restore
    the omitted null fibre. Erratum p. 5, book
    p. 258 lines 20/22 and p. 259 lines 3/4,
    supplies the source remainder as well as the target remainder. *)
Theorem rectifiable_chart_cover_fibres_countably_rectifiable (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (psi:nat->R_n R m->R_n R n)
    (C:nat->set (R_n R mu)) (gamma:nat->R_n R mu->R_n R v)
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)):
  (mu<m)%N ->is_metric_lipschitz setT F ->
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  (forall w,W w ->Z (F w)) ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) [set z|
      is_countably_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (m-mu)
        (mapping_fibre F W z)].
Proof.
move=>hDim hF hSource hTarget hRange.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose beta:=@hausdorff_measure R Y mu.
pose rho:=@hausdorff_measure R X (m-mu).
have hb:=@hausdorff_measure_is_measure R Y mu.
have hr:=@hausdorff_measure_is_measure R X (m-mu).
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
have hInverse j:exists G:R_n R v->R_n R mu,
    @is_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R v))
      (inner_metric_space (@euclidean_inner_productP R mu)) setT G lambda /\
    forall y,C j y ->G (gamma j y)=y.
  exact:(uniform_compact_chart_inverse_global_extension (hTarget.1 j).1).
have [G hG]:=choice hInverse.
have hPair (p:nat*nat):measure_almost_everywhere beta [set z|
    is_countably_measure_m_rectifiable rho (m-mu) (mapping_fibre F (P p) z)].
  have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hSource.1 p.1).1).
  have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hTarget.1 p.2).1).
  have hInv:=metric_lipschitz_of_bound (hG p.2).1.
  have hComp:=metric_lipschitz_whole_composite (metric_lipschitz_whole_composite hPsi hF) hInv.
  exact:(@lipschitz_chart_pair_fibres_countably_rectifiable R m n mu v (K p.1) (C p.2)
    (psi p.1) F (gamma p.2) (G p.2) hDim hPsi hGamma hComp (hG p.2).2).
have hCount:countable (@setT (nat*nat)).
  exact:countableP.
pose Index:=(nat*nat)%type.
have hAll:=@measure_almost_everywhere_countable R [the choiceType of Y]
  [the choiceType of (Index:Type)] beta hb setT
  (fun p=>[set z|is_countably_measure_m_rectifiable rho (m-mu) (mapping_fibre F (P p) z)])
  hCount (fun p _=>hPair p).
have hOmitted:=@rectifiable_chart_pair_omitted_fibres_null R m n mu v lambda W Z K psi C gamma F
  (ltnW hDim) hF hSource hTarget hRange.
have hBoth:=measure_almost_everywhere_and hb hAll hOmitted.
apply:(measure_almost_everywhere_mono hb _ hBoth)=>z [hPieces hNull].
have hCover:is_countably_measure_m_rectifiable rho (m-mu)
    (\bigcup_(p in @setT (nat*nat)) mapping_fibre F (P p) z).
  exact:(countably_measure_rectifiable_countable_union hr hCount (fun p _=>hPieces p Logic.I)).
apply:(countably_measure_rectifiable_null_remainder hCover).
have hEq:=@mapping_fibre_chart_remainder X Y (nat*nat)%type F W setT P z.
by rewrite -hEq.
Qed.
