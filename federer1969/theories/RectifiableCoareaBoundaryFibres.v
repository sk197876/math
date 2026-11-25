(** Federer (1969), 3.2.22(2), p. 258: the
    equal-dimension and zero-target-degree fibre conclusions.
    These boundaries use counting measure and hereditary
    source rectifiability rather than a strict-dimension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableSetUP MeasureRectifiableSubset FiniteHausdorffZeroRectifiability
  HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic
  RectifiableCoareaRemainders FiniteHausdorffFibres.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_zero_target_degree_fibres]:
    mu=0 case of Federer 3.2.22(2), p. 258.
    Each fibre is a subset of the finite-mass
    (H^m,m) rectifiable source. The actual fibre
    measurability follows from 2.10.26; no positive
    target degree or finite target cardinality premise is added. *)
Theorem rectifiable_coarea_zero_target_degree_fibres (R:realType) n k m
    (W:set (R_n R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_metric_lipschitz setT F ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) 0) [set z|
      is_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) m (mapping_fibre F W z) /\
      measure_measurable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) (mapping_fibre F W z)].
Proof.
move=>hRect hW hF.
have hMeas:=@rectifiable_coarea_fibre_measurability R n k m 0 F W (leq0n m) hF hW hRect.2.
rewrite subn0 in hMeas.
apply:(measure_almost_everywhere_mono (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R k)) 0) _ hMeas.2)=>z hMz.
split; last exact hMz.
exact:(@measure_rectifiable_subset R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m W
  (mapping_fibre F W z) (fun x hx=>hx.1) hRect).
Qed.

(** Source for [rectifiable_coarea_equal_dimension_fibres]:
    m=mu case of Federer 3.2.22(2), p. 258.
    The general fibre bound makes almost every H^0
    fibre finite, hence zero rectifiable; 2.10.26
    gives actual measurability. This supporting result
    needs only finite measurable H^m source mass. *)
Theorem rectifiable_coarea_equal_dimension_fibres (R:realType) n k m
    (W:set (R_n R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)):
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  is_metric_lipschitz setT F ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) m) [set z|
      is_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) 0) 0 (mapping_fibre F W z) /\
      measure_measurable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) 0) (mapping_fibre F W z)].
Proof.
move=>hW hFinite hF.
have hMeas:=@rectifiable_coarea_fibre_measurability R n k m m F W (leqnn m) hF hW hFinite.
have hFin:=@finite_hausdorff_fibres_almost R n k m m F W (leqnn m) hF hFinite.
rewrite subnn in hMeas hFin.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R k)) m.
have hBoth:=measure_almost_everywhere_and hb hFin hMeas.2.
apply:(measure_almost_everywhere_mono hb _ hBoth)=>z [hFz hMz].
split; last exact hMz; exact:(finite_hausdorff_zero_rectifiable hFz).
Qed.
