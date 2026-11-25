(** Federer (1969), 3.2.25, p. 261: the measurable-source
    case of the printed orientation lemma. Compact charts supply
    normalized differential words; exact Borel pieces glue without
    an outside value. The nonmeasurable-source reduction is separate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ModuleQuotient Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  NormDifferentialUP NormDifferentialDirectional LipschitzUP LipschitzBasic PartialFunctionUP
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts RectifiableCompactChartLaws
  RectifiableOrientationUP RectifiableChartOrientation EuclideanDifferentialOrientation
  EuclideanDifferentialOrientationContinuity RectifiableDensityTangent RectifiableChartDensityDifferential
  RectifiableDifferentialChartUP RectifiableTangentPlaneUP MeasureApproximateTangentUP
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction BorelRegularMeasureUP TopologicalBorel BorelPartialGluing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_measurable_orientation_borel]: the
    measurable-W proof of Federer 3.2.25, p. 261. The
    resulting partial field has Borel open preimages and simple
    unit values at every defined point. Its actual associated
    m-plane is the approximate tangent almost everywhere. The
    proof follows 3.2.18 and 3.2.19 as printed, with all
    natural dimension boundaries and the corrected H^m qualifier. *)
Theorem rectifiable_measurable_orientation_borel (R:realType) m n (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  let E:=inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R)
    (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) in
  exists T:partial_function (R_n R n) (exterior_power (R_n R n) m),
    (forall U:set E,open U ->@borel_set (inner_metric_space (@euclidean_inner_productP R n))
      (partial_function_preimage T U)) /\is_rectifiable_measurable_orientation W T.
Proof.
move=>hRect hW E.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have hTwoPositive:(0<(2:R))%R by rewrite ltr0n.
have [K [psi hCover]]:=@federer_3_2_18 R m n 2%R W hRect hW hTwo.
have hExist i:=uniform_compact_chart_orientation_exists hTwoPositive (hCover.1 i).1.
have [h hLocal]:=choice hExist.
pose P:=fun i=>psi i @` K i.
have hPBorel i:@borel_set X (P i).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X)
    (uniform_compact_chart_image_compact (hCover.1 i).1))).
have [T [hGlue [hDomain hTBorel]]]:=@borel_partial_gluing_exists X E [the choiceType of (nat:Type)]
  setT P h (countableP setT) (fun i _=>hPBorel i) (fun i _=>(hLocal i).1)
  (fun i j _ _=>hCover.2.1 i j).
have hRange w xi:partial_function_graph T w xi ->
    simple xi /\@exterior_norm R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m xi= 1.
  move=>hGraph; have [i [_ [hPi hValue]]]:=(hGlue w xi).1 hGraph.
  have [a ha hpsi]:=hPi.
  have [D [hD [hInjective [hOrientation [hSimple hUnit]]]]]:=(hLocal i).2 a ha.
  rewrite hpsi in hSimple.
  rewrite hpsi in hUnit.
  rewrite hValue in hSimple.
  rewrite hValue in hUnit.
  by split.
have hZero:@is_metric_lipschitz_bound R X
    (inner_metric_space (@euclidean_inner_productP R 0)) setT (fun _=>0) 0.
  split; first exact:lexx.
  by move=>x y _ _; rewrite mdistxx mul0r.
pose F:=fun _:R_n R n=>(0:R_n R 0).
pose Q:=fun i=>[set w|P i w ->is_rectifiable_differential_chart_point W (K i) (psi i) F w].
have hOne i:measure_almost_everywhere H (Q i).
  have hRaw:=rectifiable_chart_density_differential hTwo (hCover.1 i).1 (hCover.1 i).2
    hW hRect.2 (metric_lipschitz_of_bound hZero).
  have hImp:=(measure_almost_everywhere_on_implication _ _ _).1 hRaw.
  apply:(measure_almost_everywhere_mono hH _ hImp)=>w hw hPi; exact:(hw hPi).2.
have hAll:=measure_almost_everywhere_countable hH (countableP (@setT nat)) (fun i _=>hOne i).
have hCovered:measure_almost_everywhere H [set w|W w ->(\bigcup_i P i) w].
  exact:(measure_almost_everywhere_on_implication _ _ _).1 hCover.2.2.
have hPlane:=(measure_almost_everywhere_on_implication _ _ _).1 (federer_3_2_19 hRect hW).1.
have hBoth:=measure_almost_everywhere_and hH hAll (measure_almost_everywhere_and hH hCovered hPlane).
exists T; split; first exact hTBorel; constructor.
- apply:(borel_partial_measurable_on hH (@hausdorff_measure_borel_regular R X m) hTBorel).
  by rewrite hDomain; exact hCover.2.2.
- exact hRange.
- apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hH _ hBoth)=>w [hEvery [hInCover hInPlane]] hw.
  have [i _ hPi]:=hInCover hw.
  have hPoint:=hEvery i Logic.I hPi.
  have [a ha hpsi]:=hPi.
  have [D [hD [hInjective [hValue hUnit]]]]:=(hLocal i).2 a ha.
  have [a0 [D0 [L0 [d0 [ha0 [hpsi0 [hInjective0 [hD0 [hL0 [hCone hExtra]]]]]]]]]]:=hPoint.
  have hParam:a0=a:=@uniform_compact_chart_injective R m n 2%R (K i) (psi i)
    (hCover.1 i).1 a0 a ha0 ha (eq_trans hpsi0 (esym hpsi)).
  rewrite hParam in hD0.
  have hDerivative:D=D0:=@norm_differential_unique R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT (psi i) a D D0 hD hD0.
  rewrite -hDerivative in hCone.
  rewrite hpsi in hValue.
  exists (h i w); split.
  + apply:(hGlue w _).2; exists i; split; first exact Logic.I; by split.
  + split; last exact:(hInPlane hw).2.
    rewrite hValue; exact:(eq_trans hCone (esym (euclidean_differential_orientation_associated hInjective))).
Qed.
