(** Federer (1969), 3.2.13, p. 250: the
    m=1 radial coarea identity follows from
    weighted area and the exact two-point H^0
    fibre integrals. No higher-dimensional coarea hypothesis
    is applied at this boundary dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanOneCoordinate EuclideanRadialDifferential RadialCoareaJacobian RadialSphereIntegral RadialLineSphere
  RadialLineFibreSum RadialPolarFirstHigh EuclideanLebesgueDimensions ApproximateDifferentialAffine
  EuclideanHausdorffLebesgue HausdorffMeasure AreaWeightedFormula CoareaFibreIntegral
  PartialFunctionUP PartialFunctionBasic PartialFibreNumericalSum PartialFunctionPrecomposition PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  LipschitzUP SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_line_area_coarea_agreement]: numerical
    area sums and the actual H^0 sphere
    integrals agree outside the null zero target,
    supporting Federer 3.2.13, p. 250. *)
Lemma radial_line_area_coarea_agreement (R:realType) (g:R_n R 1->R):
  measure_almost_equal (@euclidean_lebesgue_measure R 1)
    (partial_fibre_numerical_sum (@euclidean_radial_norm R 1) (real_total_integrand g))
    (coarea_fibre_integral (@euclidean_radial_norm R 1) (real_total_integrand g)).
Proof.
pose mu:=@euclidean_lebesgue_measure R 1.
pose hm:=euclidean_lebesgue_is_measure R 1.
have hAway:measure_almost_everywhere mu (~` [set (0%R:R_n R 1)]).
  by rewrite /measure_almost_everywhere setCK; exact:positive_euclidean_singleton_null.
apply:(measure_almost_everywhere_mono hm _ hAway)=>y hy.
pose r:=euclidean_one_project y.
have hr0:(r!=0)%R.
  apply/eqP=>he; apply:hy.
  have hEq:y=euclidean_one_embed (0%R:R).
    have hValue:euclidean_one_project y=0%R by exact he.
    by rewrite -(euclidean_one_projectK y) hValue.
  rewrite hEq; apply/ffunP=>i; by rewrite /euclidean_one_embed !ffunE.
case:(ltP 0%R r)=>hr.
- exists (g (euclidean_one_embed r)+g (euclidean_one_embed (-r)%R))%R%:E; split.
  + exact:radial_line_fibre_sum_positive hr.
  + apply/radial_coarea_sphere_graph.
    exact:radial_line_sphere_integral hr.
- have hrNeg:(r<0)%R by rewrite lt_neqAle hr0 hr.
  exists 0; split.
  + exact:radial_line_fibre_sum_negative hrNeg.
  + apply/radial_coarea_sphere_graph; exact:radial_sphere_integral_negative_zero hrNeg.
Qed.

(** Source for [radial_coarea_integral_dimension_one]: the
    weighted-area proof of the m=1 case
    needed by Federer 3.2.13, p. 250.
    Both actual integrals exist with the same
    signed value, including either infinite outcome. *)
Lemma radial_coarea_integral_dimension_one (R:realType) (g:R_n R 1->R):
  is_measure_integrable (@euclidean_lebesgue_measure R 1) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R 1) (real_total_integrand g) a /\
    is_measure_integral (@euclidean_lebesgue_measure R 1)
      (coarea_fibre_integral (@euclidean_radial_norm R 1) (real_total_integrand g)) a.
Proof.
move=>[b hg].
have hLip:is_metric_lipschitz setT (@euclidean_radial_norm R 1).
  exists 1%R; split; first exact:ltr01; exact:euclidean_radial_unit_lipschitz.
have [a [hSource hTarget]]:=euclidean_weighted_area_formula hLip (ex_intro _ b hg).
have hSourceRadial:is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_density_product (real_total_integrand g)
      (EuclideanTargetJacobianMeasurable.extended_euclidean_target_jacobian (@euclidean_radial_norm R 1))) a:=hSource.
have hH:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1=
    @euclidean_lebesgue_measure R 1.
  apply:funext=>A; exact:(euclidean_hausdorff_spherical_lebesgue A).1.
rewrite hH in hTarget.
exists a; split.
- exact (measure_integral_almost_equal (euclidean_lebesgue_is_measure R 1) hSourceRadial
    (radial_jacobian_density_almost_equal (ltnSn 0) hg.1)).
- exact (measure_integral_almost_equal (euclidean_lebesgue_is_measure R 1) hTarget
    (radial_line_area_coarea_agreement g)).
Qed.
