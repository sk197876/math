(** Federer (1969), 3.2.3, pp. 243–244: univalent
    Borel pieces have their actual image mass as Jacobian
    density. This supporting all-outer-subsets form is needed
    to localize the Riemannian extension in 3.2.46, p. 282.
    Injectivity is required only on the original piece. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  EuclideanNoncenteredVitali NormMetricScaleContinuity LipschitzUP
  EuclideanAreaFormula EuclideanJacobianMeasurable JacobianDensityMeasure
  HausdorffMeasure HausdorffClosedCoverAgreement InjectiveBorelImage
  MeasureUP MeasureRestriction BorelRegularRestriction BorelRegularMeasureUP
  TopologicalBorel BorelFamilyBasic BorelMeasureAgreement DensityBorelRegular
  MeasureIntegralUP MeasureIntegralUniqueness PartitionMultiplicityIntegral
  MeasureImagePullback MeasurePieceImagePullback ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_piece_area_density]: the actual
    costs H^m(f(E intersect S)) equal the original Jacobian
    measure of E intersect S, on every outer source S,
    supporting 3.2.46, p. 282, from 3.2.3, pp. 243–244.
    A Borel E and injectivity on E suffice; no global
    injective extension or null nonmeasurable hull excess is used. *)
Theorem euclidean_piece_area_density (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (E : set (R_n R m)) :
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] E ->
  {in E &, injective f} ->
  measure_restrict (measure_image_pullback f
    (@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m)) E =
  measure_restrict (euclidean_jacobian_measure f) E.
Proof.
move=> hLip hE hInj.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose beta := @hausdorff_measure R Y m.
pose mu := measure_restrict (measure_image_pullback f beta) E.
pose nu := measure_restrict (euclidean_jacobian_measure f) E.
have hBeta := @hausdorff_measure_is_measure R Y m.
have hBetaRegular := @hausdorff_measure_borel_regular R Y m.
have hCont : continuous f.
  have [L [hL hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hIntersection B (hB : @borel_set X B) : @borel_set X (E `&` B).
  exact (@borel_family_binary_intersection X setT (@borel_set X) (borel_sets_family X) E B hE hB).
have hImageBorel B (hB : @borel_set X B) : @borel_set Y (f @` (E `&` B)).
  apply: (@injective_borel_image_borel R X Y f (E `&` B)
    (@euclidean_metric_complete R m) (@euclidean_metric_separable R m)
    (@metric_hausdorff R Y) hCont (hIntersection B hB)).
  move=> x y hx hy hEq; exact (hInj _ _ (mem_set hx.1) (mem_set hy.1) hEq).
have hMu := measure_restrict_is_measure (@measure_image_pullback_is_measure R X Y f beta hBeta) E.
have hMuRegular := @measure_piece_image_borel_regular R X Y f beta E
  hBeta hBetaRegular hE hInj hCont hImageBorel.
have hJ := euclidean_jacobian_measure_is_measure hLip.
have hNu := measure_restrict_is_measure hJ E.
have hJRegular := @density_is_borel_regular R X (@euclidean_lebesgue_measure R m)
  (euclidean_jacobian_measure f) (extended_euclidean_jacobian f)
  (euclidean_lebesgue_derivation_class R m) (euclidean_jacobian_measure_laws f)
  (extended_euclidean_jacobian_measurable hLip) (euclidean_jacobian_nonnegative_almost hLip).
have hNuRegular := @borel_regular_restrict_borel R X (euclidean_jacobian_measure f)
  hJ hJRegular E hE.
have hBorel B (hB : @borel_set X B) : mu B=nu B.
  have hEBMeas := @borel_regular_borel_measurable R X (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_borel_regular R m)
    (E `&` B) (hIntersection B hB).
  have [a [hSource hTarget]] := euclidean_area_formula hLip hEBMeas.
  have hInjective : {in E `&` B &, injective f}.
    move=> x y /set_mem [hx _] /set_mem [hy _] hEq.
    exact (hInj _ _ (mem_set hx) (mem_set hy) hEq).
  have hImageMeas := @borel_regular_borel_measurable R Y beta hBeta hBetaRegular
    (f @` (E `&` B)) (hImageBorel B hB).
  have hActual := injective_multiplicity_integral hBeta hInjective hImageMeas.
  have hImageValue : a=mu B := measure_integral_unique hTarget hActual.
  have hJacValue : a=nu B := measure_integral_unique hSource
    (euclidean_jacobian_measure_integral hLip hEBMeas).
  by rewrite -hImageValue -hJacValue.
exact (@borel_regular_measures_agree R X mu nu hMu hNu hMuRegular hNuRegular hBorel).
Qed.
