(** Federer (1969), 3.2.22(2), p. 258: the
    fibre conclusion for the original Lipschitz partial
    map with exactly domain W and image in Z. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionSourceRestriction PartialFunctionExtensionUP PartialMetricLipschitz
  EuclideanPartialLipschitzExtension PartialMappingMultiplicity RectifiableSetUP RectifiableCoareaFibres
  HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_22_2]: the complete
    assertion (2) of Federer 3.2.22, p. 258:
    for H^mu almost every z in Z, the actual
    fibre f inverse z is (H^(m-mu),m-mu) rectifiable
    and H^(m-mu)-measurable. The graph-preserving opaque
    extension is auxiliary; its values outside W never
    enter the original fibre. All printed hypotheses and
    natural-dimension boundaries are retained, with no extra
    rank, derivative field or finite-fibre premise. *)
Theorem federer_3_2_22_2 (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z [set z|
      is_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (m-mu) (partial_mapping_fibre f z) /\
      measure_measurable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (partial_mapping_fibre f z)].
Proof.
move=>hDim hRectW hW hRectZ hZ hDomain [L hLip] hRange.
have [F [hBound hEq]]:=euclidean_partial_lipschitz_global_extension hLip.
have hExt:is_partial_function_total_extension f F.
  move=>x y hxy; have hGraph:=hxy; rewrite hEq in hGraph; exact hGraph.2.
have hImage:forall x,W x ->Z (F x).
  move=>x hx.
  have hDomainX:partial_function_domain f x by rewrite hDomain.
  have [y hxy]:=hDomainX; rewrite (hExt x y hxy); apply:hRange; by exists x.
have hCore:=@rectifiable_coarea_fibres R m n mu v W Z F hDim hRectW hW hRectZ hZ
  (metric_lipschitz_of_bound hBound) hImage.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hb _ hCore)=>z [hRect hMeas] _.
have hFibre:=@partial_mapping_fibre_total_extension (R_n R n) (R_n R v) f F z hExt.
rewrite hDomain in hFibre; rewrite -hFibre in hRect hMeas.
by split.
Qed.
