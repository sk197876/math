(** Federer (1969), 3.2.32, pp. 269–270: assemble
    coarea over the positive fibre locus, without assuming
    measurability of its source inverse image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure HausdorffClosedCoverAgreement
  BorelRegularMeasureUP RectifiableSetUP PositiveFibreTargetCoverUP RectifiableBorelTargetPieces
  MeasureApproximateJacobian MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MappingMultiplicity ExtendedRealOrderTopology RectifiableRestrictedCoareaIntegral
  CountableDisjointCoareaIntegral RectifiableNullTargetJacobian SubsetIntegralZeroRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_positive_fibre_cover_integral]: the
    integral identity of Federer 3.2.32, p. 269, by
    the countable 3.2.22 applications prescribed on p. 270.
    The Borel hull excess is target null, and 3.2.22
    makes the original Jacobian vanish almost everywhere above it.
    Thus its source integral is removable even when the exact
    positive-fibre preimage has not separately been proved measurable.
    Infinite integral values and zero dimensions are retained. *)
Theorem rectifiable_positive_fibre_cover_integral (R:realType) m n mu v
    (W:set (R_n R n)) (F:R_n R n->R_n R v) (J:R_n R n->R)
    (D:nat->set (R_n R v)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  (forall x,(0<=J x)%R) ->
  is_partial_function_total_extension (measure_approximate_jacobian
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    m mu (partial_function_source_restrict W (partial_function_total F))) J ->
  @is_positive_fibre_target_cover R (inner_metric_space (@euclidean_inner_productP R v))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) mu
    [set y|0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (m-mu) (mapping_fibre F W y)] D ->
  exists a,is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (W `&` F @^-1` [set y|0<@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F W y)])
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
        (mapping_fibre F W y):extended_real_line R))) a.
Proof.
move=>hDim hRect hW hF hJPos hJ hCover.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R v).
pose H:=@hausdorff_measure R X m.
pose B:=@hausdorff_measure R T mu.
pose K:=@hausdorff_measure R X (m-mu).
pose phi y:extended_real_line R:=K (mapping_fibre F W y).
pose Y:set T:=[set y|0<phi y].
pose S i:=W `&` F @^-1` D i.
have hH:=@hausdorff_measure_is_measure R X m.
have hB:=@hausdorff_measure_is_measure R T mu.
have hK:=@hausdorff_measure_is_measure R X (m-mu).
have hPhiPos y:0<=phi y:=measure_nonnegative hK _.
have hDDisj:=positive_fibre_cover_disjoint hCover.
have hSDisj i j (hij:i!=j) x:S i x ->S j x ->False.
  move=>[_ hi] [_ hj]; exact:(hDDisj i j hij (F x) hi hj).
have hPhiOff y:~(\bigcup_i D i) y ->phi y=0.
  move=>hNot.
  have hNotPos:~(0<phi y) by move=>hy; exact:hNot (positive_fibre_cover_contains hCover hy).
  apply/eqP; rewrite eq_le (hPhiPos y) andbT leNgt; exact/negP.
have hLocal i:exists a,is_measure_subset_integral H (S i)
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral B (partial_function_total (fun y=>if pselect (D i y) then phi y else 0)) a.
  have hPiece:=@rectifiable_borel_target_piece R m n v W F (D i)
    hRect hW hF (positive_fibre_cover_borel hCover i).
  have hSub:S i `<=` W by move=>x [hx _].
  have hDMeas:=borel_regular_borel_measurable hB (@hausdorff_measure_borel_regular R T mu)
    (positive_fibre_cover_borel hCover i).
  have hRange x:S i x ->D i (F x) by move=>[_ hx]; exact hx.
  have [a [hSource hTarget]]:=@rectifiable_restricted_coarea_integral R m n mu v W (S i) (D i) F J
    hDim hRect hW hPiece.1 hSub (positive_fibre_cover_rectifiable hCover i) hDMeas hF hRange hJ.
  exists a; split; first exact hSource.
  apply:(measure_integral_graph_equivalent _ hTarget)=>y z.
  have hMass:K (mapping_fibre F (S i) y)=(if pselect (D i y) then phi y else 0).
    rewrite /S mapping_fibre_target_piece; case:pselect=>hy; first reflexivity.
    exact:measure_empty.
  change (K (mapping_fibre F (S i) y)=z <->(if pselect (D i y) then phi y else 0)=z).
  by rewrite hMass.
have [a [hSource hTarget]]:=@countable_disjoint_coarea_integral R [the choiceType of X] [the choiceType of T]
  H B hH hB S D J phi hJPos hPhiPos hSDisj hDDisj hPhiOff hLocal.
pose A:=W `&` F @^-1` Y.
pose U:=\bigcup_i S i.
pose Q:=(\bigcup_i D i) `\` Y.
have hAU:A `<=` U.
  move=>x [hx hy]; have [i _ hi]:=positive_fibre_cover_contains hCover hy.
  exists i=>//; by split.
have hZero:=@rectifiable_null_target_jacobian_zero R m n v mu W F Q J
  hRect hW hF (positive_fibre_cover_null_excess hCover) hJ.
have hRemainder:measure_almost_everywhere_on H (U `\` A) [set x|(J x)%:E=0].
  apply:(measure_null_subset hH _ hZero)=>x [[hU hNotA] hNotZero].
  have [i _ [hx hi]]:=hU.
  split.
  - split; first exact hx.
    split; first by exists i.
    by move=>hy; apply:hNotA; split.
  - move=>hJZero; apply:hNotZero; change ((J x)%:E=0); by rewrite hJZero.
exists a; split; last exact hTarget.
exact:(subset_integral_zero_remainder hH hAU hRemainder hSource).
Qed.
