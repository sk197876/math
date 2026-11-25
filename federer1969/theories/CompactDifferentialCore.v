(** Federer (1969), 3.2.38, pp. 274--275: existence of the
    compact good-point core, using only actual differential graph
    laws, finite measurable exhaustion, and the earlier Lusin theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel
  LipschitzUP Rademacher NormDifferentialUP EuclideanUniformRemainderPoints UniformRemainderRadiusLaws
  FiniteMeasureUniformRadius RealMetricBackground RealLineSeparability
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialContinuityUP
  MeasurableFunctionUP BorelFunctionUP LusinMetric CompactDifferentialCoreUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_differential_core_exists]: supporting the
    good-point selection in Federer 3.2.38, p. 274, by a compact
    scalar Lusin core. Actual Borel remainder tests exhaust the
    Rademacher domain; finite measurable continuity chooses one
    reciprocal radius. Lusin 2.3.5 makes J continuous on a further
    closed subset of C, with one total error budget. No derivative
    field, source extension or uniform remainder premise is assumed.
    This explicitly records the replacement of the printed mean-test
    selection; the subsequent two-family cube proof is preserved. *)
Theorem compact_differential_core_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R)
    (C:set (inner_metric_space (@euclidean_inner_productP R m))) (e budget:R):
  is_metric_lipschitz setT f ->is_borel_function J ->compact C ->0<e ->0<budget ->
  exists d E,is_compact_differential_core f J C e budget d E.
Proof.
move=>hLip hJ hC he hBudget.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hr:=euclidean_lebesgue_borel_regular R m.
have hCm:measure_measurable mu C.
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) hC).
have hCf:(mu C< +oo)%E:=euclidean_compact_finite hC.
pose F j:=euclidean_uniform_remainder_points f e ((j.+1%:R:R)^-1).
have hFm j:measure_measurable mu (F j).
  exact:(@borel_regular_borel_measurable R X mu hm hr _
    (euclidean_uniform_remainder_points_borel e ((j.+1%:R:R)^-1) hLip)).
have hMono j k:(j<=k)%N ->F j `<=` F k.
  move=>hjk.
  have hRadius:((k.+1%:R:R)^-1)<=((j.+1%:R:R)^-1).
    have hkPos:(0<(k.+1%:R:R))%R by rewrite ltr0n.
    have hjPos:(0<(j.+1%:R:R))%R by rewrite ltr0n.
    by rewrite (@lef_pV2 R _ _ hkPos hjPos) ler_nat.
  exact:(@euclidean_uniform_remainder_radius_monotone R m n f e
    ((k.+1%:R:R)^-1) ((j.+1%:R:R)^-1) hRadius).
have hConull:measure_almost_everywhere mu (\bigcup_j F j).
  apply:(measure_almost_everywhere_mono hm _ (federer_3_1_6 hLip))=>a [D hD].
  have [j hj]:=euclidean_uniform_remainder_reciprocal_exhaustion hD he.
  by exists j.
have hNull:mu (C `\` \bigcup_j F j)=0%E.
  exact:(@measure_null_subset R X mu hm _ _ (fun x (hx:(C `\` \bigcup_j F j) x)=>hx.2) hConull).
have hHalf:0<budget/2 by rewrite divr_gt0 // ltr0n.
have [j hj]:=finite_measure_increasing_good_sets hm hCm hCf hFm hMono hNull hHalf.
pose A:=C `&` F j.
have hAm:measure_measurable mu A:=measure_measurable_intersection hm hCm (hFm j).
have hAf:(mu A< +oo)%E.
  exact:le_lt_trans (measure_mono hm (fun x (hx:A x)=>hx.1)) hCf.
have hJm:is_measure_measurable_function mu (partial_function_total J).
  constructor.
  - rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
  - move=>U hU; rewrite partial_function_total_preimage.
    exact:(@borel_regular_borel_measurable R X mu hm hr _ (hJ U hU)).
have [D [hDc hDd]]:=real_line_countable_dense R.
have [E [hE [hEA [hError hContinuous]]]]:=
  @lusin_borel_regular R X (real_line_metric R) mu hm hr D A (partial_function_total J)
    (budget/2) hDc hDd hJm hAm hAf hHalf.
have hEC:E `<=` C by move=>x hx; exact:(hEA x hx).1.
have hCompact:compact E:=subclosed_compact hE hC hEC.
have hCover:(C `\` E) `<=` (C `\` F j) `|` (A `\` E).
  move=>x [hx hn]; case:(pselect (F j x))=>hF; [right; split=>//; by split|left; by split].
have hTotal:(mu (C `\` E)<budget%:E)%E.
  apply:le_lt_trans (measure_binary_cover hm hCover) _.
  have hErrorFinite:mu (A `\` E) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact:lt_trans hError (ltry _).
  have hSum:=lte_leD hErrorFinite hj (ltW hError).
  by rewrite -EFinD -splitr in hSum.
exists ((j.+1%:R:R)^-1),E; split=>//; split=>//; split=>//.
split; first by rewrite invr_gt0 ltr0n.
split; last exact hContinuous.
by move=>x hx; exact:(hEA x hx).2.
Qed.
