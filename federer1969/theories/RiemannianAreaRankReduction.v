(** Federer (1969), 3.2.5, pp. 244–245, extended
    by 3.2.46, p. 282: actual positive-rank source
    null-preimage control and null nonpositive-rank image.
    The actual area formula and original Borel regularity
    discharge both reductions without assuming arbitrary
    completed target preimages measurable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianMapJacobian
  RiemannianAreaJacobianVolumeMeasurable RiemannianLocalAreaSelection
  RiemannianBorelAreaSelection RiemannianUnweightedArea
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureFiniteClosure
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages
  NormMetricScaleContinuity LipschitzUP MappingMultiplicity MappingMultiplicityLaws
  MeasurableFunctionUP PartialExtendedOrderLoci ZeroExtensionNonnegative
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  MeasureConullZeroIntegral MeasureNonnegativeZero CountableOrderIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_positive_area_locus_measurable]:
    the actual positive Jacobian locus is source-measurable,
    supporting 3.2.46, p. 282, and the cutoff
    in 3.2.5, p. 245. The domain remains the
    original differential domain, with no assigned values. *)
Lemma riemannian_positive_area_locus_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) (positive_riemannian_area_locus f).
Proof.
move=> hLip.
have hJ := @riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip.
have hEqual : positive_riemannian_area_locus f=
    partial_function_preimage (extended_riemannian_map_jacobian f m)
      [set y : extended_real_line R | (0<y)%E].
  apply/seteqP; split=> x.
  - move=> [r [hr hR]]; exists r%:E; split; first by exists r; split.
    exact hR.
  - move=> [z [[r [hr <-]] hZ]]; exists r; split; first exact hr.
    exact hZ.
rewrite hEqual.
apply: (@measurable_function_open_preimage R [the choiceType of riemannian_metric_space hg]
  (extended_real_line R) (riemannian_hausdorff_measure hg m%:R hp)
  (extended_riemannian_map_jacobian f m) hJ _).
exact: order_strict_upper_ray_open.
Qed.

(** Source for [riemannian_positive_area_null_preimage]:
    target null sets have null original positive-Jacobian
    preimages, supporting alternatives (1) and (2) of
    3.2.5, p. 245, in 3.2.46, p. 282.
    A true null Borel cover first gives a measurable
    test set; the actual area formula then forces zero
    integral, and positivity gives source nullity. *)
Theorem riemannian_positive_area_null_preimage (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) N :
  is_riemannian_path_lipschitz f -> riemannian_hausdorff_measure hh m%:R hp N=0%E ->
  riemannian_hausdorff_measure hg m%:R hp
    (positive_riemannian_area_locus f `&` (f @^-1` N))=0%E.
Proof.
move=> hLip hNull.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
pose P := positive_riemannian_area_locus f.
pose J := extended_riemannian_map_jacobian f m.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have [D [hND [hD hMass]]] := borel_regular_cover
  (@riemannian_hausdorff_borel_regular R n B h hh m%:R hp) N.
have hDNull : beta D=0%E.
  change (riemannian_hausdorff_measure hh m%:R hp D=0%E); by rewrite -hMass.
have hCont : continuous f.
  have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
pose E := P `&` (f @^-1` D).
have hPreD := @borel_regular_borel_measurable R X mu hMu
  (@riemannian_hausdorff_borel_regular R m A g hg m%:R hp) (f @^-1` D)
  (@continuous_borel_preimage X Y f hCont D hD).
have hE := @measure_measurable_intersection R X mu hMu P (f @^-1` D)
  (@riemannian_positive_area_locus_measurable R m n A B g h hg hh f hp hLip) hPreD.
have [a [hSource hTarget]] := @riemannian_unweighted_area_formula R m n A B g h hg hh f hp E hLip hE.
have hZeroTarget : is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f E y : extended_real_line R))) 0%E.
  apply: (@measure_almost_zero_integral R Y beta hBeta).
  have hOff : measure_almost_everywhere beta (~`D) by rewrite /measure_almost_everywhere setCK.
  apply: (@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hOff)=> y hy.
  apply: (@mapping_multiplicity_zero_iff R X Y f E y).2.
  move=> [x hx hxy]; apply: hy; rewrite -hxy; exact hx.2.
have hA : a=0%E := measure_integral_unique hTarget hZeroTarget.
rewrite hA in hSource.
pose K := partial_function_zero_extension (0%E : extended_real_line R) E J.
have hPositive := @zero_extension_nonnegative_almost R X mu hMu E J
  (@riemannian_area_jacobian_volume_nonnegative R m n A B g h hg hh f hp hLip).
have hZeroSource := @nonnegative_integral_zero_almost_equal R X mu hMu K hSource hPositive.
have hOffE : measure_almost_everywhere mu (~`E).
  apply: (@measure_almost_everywhere_mono R X mu hMu _ _ _ hZeroSource)=> x [z [hz hZ]] hx.
  have [r [hr hR]] := hx.1.
  have hKValue : partial_function_graph K x r%:E.
    apply/partial_function_zero_extension_graph; left; split; first exact hx.
    exists r; by split.
  have hValue := partial_function_single_valued hKValue hz.
  have hRZero : r%:E=0%E := eq_trans hValue (esym hZ).
  have hRPositive : (0<r%:E)%E by rewrite lte_fin.
  by rewrite hRZero ltxx in hRPositive.
have hENull : mu E=0%E by move: hOffE; rewrite /measure_almost_everywhere setCK.
apply: (@measure_null_subset R X mu hMu _ E _ hENull).
move=> x [hx hN]; split; first exact hx; exact: hND (f x) hN.
Qed.

(** Source for [riemannian_nonpositive_area_image_null]:
    the actual nonpositive or undefined Jacobian image is
    null, supporting 3.2.5, p. 245, in 3.2.46,
    p. 282. Apply the proved original-domain Borel
    selection to its complement: its positive-Jacobian
    selected subset is empty. No rank field is assumed. *)
Theorem riemannian_nonpositive_area_image_null (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_riemannian_path_lipschitz f ->
  riemannian_hausdorff_measure hh m%:R hp (f @` (~`positive_riemannian_area_locus f))=0%E.
Proof.
move=> hLip.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hP := @riemannian_positive_area_locus_measurable R m n A B g h hg hh f hp hLip.
have [W [hW [hWSub [hWInj [hWImage hDeficit]]]]] := @riemannian_borel_area_selection R m n A B g h hg hh
  f hp (~`positive_riemannian_area_locus f) hLip (measure_measurable_complement hP).
have hEmpty : W=set0.
  apply/seteqP; split=> x; last by [].
  move=> hx; have [hNot hIn] := hWSub x hx; exact: hNot hIn.
by rewrite hEmpty image_set0 setD0 in hDeficit.
Qed.
