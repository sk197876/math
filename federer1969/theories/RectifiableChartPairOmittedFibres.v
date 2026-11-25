(** Federer (1969), 3.2.22, pp. 258–259:
    after removing all chart-pair pieces, the omitted
    source has null complementary fibres almost everywhere.
    This retains both erratum source R and target Q. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableCompactChartsUP RectifiableChartPairPieces RectifiableChartPairFamily RectifiableCoareaRemainders
  HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_chart_pair_omitted_fibres_null]:
    the omitted fibres in Federer 3.2.22, pp. 258–259.
    Outside the H^mu-null target remainder Q, the
    omitted fibre lies in the source-chart remainder R.
    Erratum p. 5, book p. 258 lines 20/22
    and p. 259 lines 3/4, retains R and proves
    its H^(m-mu)-null fibres almost everywhere. *)
Theorem rectifiable_chart_pair_omitted_fibres_null (R:realType) m n mu v
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
    (inner_metric_space (@euclidean_inner_productP R v)) mu)
    [set z|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
      (mapping_fibre F (W `\` (\bigcup_(p in @setT (nat*nat))
        rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2))) z)=0].
Proof.
move=>hDim hF hSource hTarget hRange.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose beta:=@hausdorff_measure R Y mu.
have hb:=@hausdorff_measure_is_measure R Y mu.
pose SrcR:=W `\` (\bigcup_i psi i @` K i).
pose TarQ:=Z `\` (\bigcup_j gamma j @` C j).
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
have hR:=@rectifiable_coarea_null_source_remainder R n v m mu F SrcR hDim hF hSource.2.2.
have hQ:beta TarQ=0:=hTarget.2.2.
have hOutside:measure_almost_everywhere beta (~` TarQ).
  by rewrite /measure_almost_everywhere setCK.
have hBoth:=measure_almost_everywhere_and hb hOutside hR.
have hCover:=@rectifiable_chart_pair_remainder_cover R m n mu v lambda W Z K psi C gamma F
  hSource hTarget hRange.
change (W=((W `&` (F @^-1` TarQ)) `|` (\bigcup_(p in @setT (nat*nat)) P p)) `|` SrcR) in hCover.
apply:(measure_almost_everywhere_mono hb _ hBoth)=>z [hNotQ hRz].
apply:(measure_null_subset (@hausdorff_measure_is_measure R X (m-mu)) _ hRz)=>x [[hw hNotP] hValue].
have hwCover:=hw; rewrite hCover in hwCover.
have [[[hWx hQx]|hPx]|hRx]:=hwCover.
- exfalso; apply:hNotQ; change (TarQ (F x)) in hQx; by rewrite hValue in hQx.
- exfalso; exact:(hNotP hPx).
- by split.
Qed.
