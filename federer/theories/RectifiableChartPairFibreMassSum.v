(** Federer (1969), 3.2.22, pp. 259–260:
    the total fibre mass is the sum of the compact
    chart-pair fibre masses almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  NormMetricScaleContinuity RectifiableCompactChartsUP RectifiableChartPairPieces RectifiableChartPairFamily
  CompactRectifiableChartPairs CompactFibreMeasurability MappingFibreMeasureDisjointCover
  RectifiableChartPairOmittedFibres MappingMultiplicity HausdorffMeasure NonnegativeSum
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_chart_pair_fibre_mass_sum]:
    the second double sum on p. 259 in Federer
    3.2.22. Every chart-pair subfibre is compact
    and measurable. Countable additivity, disjointness
    and the omitted null fibre give the exact sum
    almost everywhere. Apply erratum p. 5, book
    p. 259 lines 3/4, to the source remainder
    as well as the target remainder. *)
Theorem rectifiable_chart_pair_fibre_mass_sum (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (psi:nat->R_n R m->R_n R n)
    (C:nat->set (R_n R mu)) (gamma:nat->R_n R mu->R_n R v)
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)):
  (mu<=m)%N ->is_metric_lipschitz setT F ->
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  (forall w,W w ->Z (F w)) ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) [set z|
      nonnegative_sum setT (fun p:nat*nat=>@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
        (mapping_fibre F (rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2)) z))=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F W z)].
Proof.
move=>hDim hF hSource hTarget hRange.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X (m-mu).
pose beta:=@hausdorff_measure R Y mu.
have hr:=@hausdorff_measure_is_measure R X (m-mu).
have hb:=@hausdorff_measure_is_measure R Y mu.
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
have hSub p:P p `<=` W by move=>w [hw _]; exact:((hSource.1 p.1).2 w hw).
have hDisjoint:forall p q,setT p ->setT q ->p<>q ->P p `&` P q=set0.
  move=>p q _ _; exact:(@rectifiable_chart_pair_pieces_disjoint R m n mu v lambda W Z K psi C gamma F hSource hTarget p q).
have hFCont:continuous F.
  have [L [hL hB]]:=hF; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
have hCompact p:@compact X (P p).
  have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hSource.1 p.1).1).
  have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound (hTarget.1 p.2).1).
  have hPsiCont:continuous (psi p.1:inner_metric_space (@euclidean_inner_productP R m)->X).
    have [L [hL hB]]:=hPsi; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
    exact:(hB.2 a b Logic.I Logic.I).
  have hGammaCont:continuous (gamma p.2:inner_metric_space (@euclidean_inner_productP R mu)->Y).
    have [L [hL hB]]:=hGamma; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
    exact:(hB.2 a b Logic.I Logic.I).
  exact:(compact_rectifiable_chart_pair_piece
    (rectifiable_chart_compact (hSource.1 p.1).1) (rectifiable_chart_compact (hTarget.1 p.2).1)
    hPsiCont hFCont hGammaCont).
have hNull:=@rectifiable_chart_pair_omitted_fibres_null R m n mu v lambda W Z K psi C gamma F
  hDim hF hSource hTarget hRange.
have hCount:countable (@setT (nat*nat)) by exact:countableP.
pose Index:=(nat*nat)%type.
apply:(measure_almost_everywhere_mono hb _ hNull)=>z hz.
symmetry; apply:(@mapping_fibre_measure_disjoint_cover R [the choiceType of X]
  [the choiceType of (Index:Type)] Y rho hr F W setT P z hCount
  (fun p _=>hSub p) hDisjoint _ hz)=>p _.
exact:(compact_hausdorff_fibres_measurable (m-mu) hFCont (hCompact p) z).
Qed.
