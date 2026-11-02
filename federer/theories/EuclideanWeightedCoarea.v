(** Federer (1969), 3.2.12, pp. 249–250: the
    weighted coarea formula, including actual partial integrands.
    Characteristic approximation, signed parts and null-fibre
    transport discharge all inner-integrability obligations. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanTargetJacobianMeasurable CoareaSignedTotal CoareaFibreIntegral CoareaFibreNullChange
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP PartialFunctionExtensionSealed
  PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality MeasureDensityTransfer
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_weighted_coarea_formula]: the
    approximation proof of Federer 3.2.12, p. 250,
    extended to the exact original partial integrand domain.
    Infinite signed values are permitted; no summability,
    independent fibre measurability or inner integrability is assumed. *)
Theorem euclidean_weighted_coarea_formula (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:partial_function (R_n R m) (extended_real_line R)):
  (n<m)%N ->is_metric_lipschitz setT f ->
  is_measure_integrable (@euclidean_lebesgue_measure R m) u ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product u (extended_euclidean_target_jacobian f)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n) (coarea_fibre_integral f u) a.
Proof.
move=>hnm hf [b hu].
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose U:=@PartialFunctionExtension.value _ (extended_real_line R) u 0.
have hExt:is_partial_function_total_extension u U:=@PartialFunctionExtension.laws _ _ u 0.
have hEqual:measure_almost_equal mu u (partial_function_total U).
  apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _ (measurable_function_domain hu.1))=>x [j hj].
  exists j; split=> //; exact (hExt x j hj).
have hU:=measure_integral_almost_equal hm hu hEqual.
have [a [hLeft hRight]]:=coarea_signed_total_integral hnm hf (ex_intro _ b hU).
exists a; split.
- apply:(measure_integral_almost_equal hm hLeft).
  apply:(partial_density_product_almost_equal hm (measure_almost_equal_sym hEqual)).
  exact ((measure_almost_equal_self _ _).2
    (measurable_function_domain (extended_euclidean_target_jacobian_measurable hf))).
- exact (coarea_fibre_integral_null_change (ltnW hnm) hf (measure_almost_equal_sym hEqual) hRight).
Qed.

(** Source for [federer_3_2_12]: Federer 3.2.12,
    pp. 249–250: for every Lebesgue-integrable real-valued g,
    the integral of g J_n f equals the iterated
    integral of g on the complementary Hausdorff fibres.
    The printed m>n and integrability hypotheses are exact;
    summability and n>0 are not imposed. *)
Theorem federer_3_2_12 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (g:R_n R m->R):
  (n<m)%N ->is_metric_lipschitz setT f ->
  is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product (real_total_integrand g) (extended_euclidean_target_jacobian f)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (coarea_fibre_integral f (real_total_integrand g)) a.
Proof. exact:euclidean_weighted_coarea_formula. Qed.
