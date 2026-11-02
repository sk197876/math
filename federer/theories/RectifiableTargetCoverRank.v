(** Federer (1969), 3.2.32, pp. 269–270: assemble
    the image-dimension bound over the countable Borel target cover.
    All differential data remain relative to the original source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure HausdorffClosedCoverAgreement
  BorelRegularMeasureUP RectifiableSetUP PositiveFibreTargetCoverUP RectifiableBorelTargetPieces
  MeasureApproximateDifferentialUP PartialImageDimensionUP RectifiableCoareaImageDimension
  RectifiableSubsetApproximateData.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_target_cover_image_dimension]: the
    exceptional-set conclusion of Federer 3.2.32, p. 269,
    after the countable applications of 3.2.22 prescribed on
    p. 270. The cover's Borel laws prove all source-piece
    measurability. Exact differential agreement retains the original
    partial domain and density measure; no preimage measurability
    of Y, rank hypothesis or derivative field is assumed. *)
Theorem rectifiable_target_cover_image_dimension (R:realType) m n mu v
    (W:set (R_n R n)) (Y:set (R_n R v)) (D:nat->set (R_n R v))
    (F:R_n R n->R_n R v):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  @is_positive_fibre_target_cover R (inner_metric_space (@euclidean_inner_productP R v))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Y D ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (W `&` F @^-1` Y) [set x|
      exists d,is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
        m (partial_function_source_restrict W (partial_function_total F)) x d /\
        is_partial_image_dimension_at_most mu d].
Proof.
move=>hRect hW hF hCover.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R v).
pose H:=@hausdorff_measure R X m.
pose B:=@hausdorff_measure R T mu.
have hH:=@hausdorff_measure_is_measure R X m.
have hB:=@hausdorff_measure_is_measure R T mu.
pose S i:=W `&` F @^-1` D i.
pose Good:set X:=[set x|exists d,is_measure_approximate_differential
  (inner_norm (@euclidean_inner_productP R v)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  (measure_restrict H W) m (partial_function_source_restrict W (partial_function_total F)) x d /\
  is_partial_image_dimension_at_most mu d].
have hEach i:measure_almost_everywhere_on H (S i) Good.
  have hPiece:=@rectifiable_borel_target_piece R m n v W F (D i)
    hRect hW hF (positive_fibre_cover_borel hCover i).
  have hDMeas:=borel_regular_borel_measurable hB (@hausdorff_measure_borel_regular R T mu)
    (positive_fibre_cover_borel hCover i).
  have hRange x:S i x ->D i (F x) by move=>[_ hx]; exact hx.
  have hRank:=@rectifiable_coarea_image_dimension_almost R m n mu v (S i) (D i) F
    hPiece.2 hPiece.1 (positive_fibre_cover_rectifiable hCover i) hDMeas hF hRange.
  have hSub:S i `<=` W by move=>x [hx _].
  have hData:=@rectifiable_subset_approximate_data_agreement R m n v W (S i) F mu
    hRect hW hPiece.1 hSub hF.
  have hBoth:=measure_almost_everywhere_and hH
    ((measure_almost_everywhere_on_implication _ _ _).1 hRank)
    ((measure_almost_everywhere_on_implication _ _ _).1 hData).
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hH _ hBoth)=>x [hR hA] hx.
  have [d [hd hDim]]:=hR hx.
  exists d; split; last exact hDim; exact:((hA hx).1 d).2 hd.
have hAll:=measure_almost_everywhere_countable hH (countableP (@setT nat))
  (fun i _=>(measure_almost_everywhere_on_implication _ _ _).1 (hEach i)).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hAll)=>x hEvery [hx hy].
have [i _ hi]:=positive_fibre_cover_contains hCover hy.
apply:(hEvery i Logic.I); by split.
Qed.
