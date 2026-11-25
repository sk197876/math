(** Federer (1969), 3.2.3(2), p. 243: the weighted
    area formula with original partial integrand domains,
    exact numerical fibre sums and infinite signed integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed PartialFibreNumericalSum FibreNumericalIntegrand
  PartialDensityProduct EuclideanJacobianMeasurable LipschitzUP HausdorffMeasure NullLipschitzArea
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureDensityTransfer AreaSignedTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_weighted_area_formula]: Federer
    3.2.3(2), p. 243, by characteristic approximation,
    the two signed parts, and removal of the null undefined
    set using 2.10.11 and 2.10.35. The fibre graph has
    a value exactly when all its inputs and the numerical
    sum are defined. No total extension enters the statement. *)
Theorem euclidean_weighted_area_formula (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:partial_function (R_n R m) (extended_real_line R)):
  is_metric_lipschitz setT f ->
  is_measure_integrable (@euclidean_lebesgue_measure R m) u ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product u (extended_euclidean_jacobian f)) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_fibre_numerical_sum f u) a.
Proof.
move=>hLip [b hu].
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
pose U:=@PartialFunctionExtension.value _ (extended_real_line R) u 0.
have hExt:is_partial_function_total_extension u U:=@PartialFunctionExtension.laws _ _ u 0.
have hEqual:measure_almost_equal mu u (partial_function_total U).
  apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _ (measurable_function_domain hu.1)).
  move=>x [j hj]; exists j; split=>//; exact (hExt x j hj).
have hU:=measure_integral_almost_equal hm hu hEqual.
have [a [hLeft hRight]]:=area_signed_total_integral hLip (ex_intro _ b hU).
exists a; split.
- apply:(measure_integral_almost_equal hm hLeft).
  apply:(partial_density_product_almost_equal hm (measure_almost_equal_sym hEqual)).
  exact ((measure_almost_equal_self _ _).2
    (measurable_function_domain (extended_euclidean_jacobian_measurable hLip))).
- pose N:=~` partial_function_domain u.
  have hN:mu N=0:=measurable_function_domain hu.1.
  have hHausN:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m N=0.
    by rewrite (euclidean_hausdorff_spherical_lebesgue N).1.
  have [M [hM hMBound]]:=hLip.
  have hImage:beta (f @` N)=0:=null_hausdorff_lipschitz_image hMBound hHausN.
  have hOff:measure_almost_everywhere beta (~` (f @` N)).
    by rewrite /measure_almost_everywhere setCK.
  apply:(measure_integral_almost_equal hb hRight).
  apply:(@measure_almost_everywhere_mono R _ beta hb _ _ _
    (measure_almost_everywhere_and hb hOff (measurable_function_domain hRight.1))).
  move=>y [hy [z hz]]; exists z; split=>//.
  have hDom:forall x,f x=y -> partial_function_domain u x.
    move=>x hxy; apply:contrapT=>hx; apply:hy; exists x=>//.
  exact ((@partial_fibre_numerical_sum_extension_graph R _ _ f u U y z hExt hDom).2
    ((@fibre_numerical_integrand_graph R _ _ f U y z).1 hz)).
Qed.

(** Source for [federer_3_2_3_2]: Federer 3.2.3(2),
    p. 243, retaining the printed m<=n hypothesis and
    integrability, rather than the stronger summability
    hypothesis. Both displayed integrals are proved to exist. *)
Theorem federer_3_2_3_2 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:partial_function (R_n R m) (extended_real_line R)):
  (m<=n)%N -> is_metric_lipschitz setT f ->
  is_measure_integrable (@euclidean_lebesgue_measure R m) u ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product u (extended_euclidean_jacobian f)) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_fibre_numerical_sum f u) a.
Proof. move=>hmn; exact:euclidean_weighted_area_formula. Qed.
