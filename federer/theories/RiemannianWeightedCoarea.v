(** Federer (1969), 3.2.46, p. 282: the
    weighted coarea formula 3.2.12, pp. 249–250,
    holds for the actual original Riemannian metrics.
    Signed parts and null-fibre transport retain original
    partial weights, infinite signed values and exact
    inner-integrability domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianPathLipschitz RiemannianMapJacobian RiemannianCoareaJacobianMeasurable
  RiemannianCoareaSignedTotal RiemannianCoareaFibreIntegral RiemannianCoareaFibreNullChange
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP PartialFunctionExtensionSealed
  PartialDensityProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality MeasureDensityTransfer
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_weighted_coarea_formula]:
    the full weighted coarea formula asserted in
    3.2.46, p. 282, extending the actual
    approximation argument of 3.2.12, p. 250.
    Exactly n<m, original path-Lipschitz continuity
    and original source-integrability are assumed.
    Actual whole fibres, original partial domains,
    singular maps, zero target dimension, signed
    infinite integrals and undefined infinity differences
    keep their actual meanings; summability, finite
    mass and independent fibre integrability are not added. *)
Theorem riemannian_weighted_coarea_formula (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : (0<=m%:R :> R)%R) (hpTarget : (0<=n%:R :> R)%R)
    (hpFibre : (0<=(m-n)%:R :> R)%R)
    (u : partial_function (riemannian_metric_space hg) (extended_real_line R)) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  is_measure_integrable (riemannian_hausdorff_measure hg m%:R hpSource) u ->
  exists a, is_measure_integral (riemannian_hausdorff_measure hg m%:R hpSource)
      (partial_density_product u (extended_riemannian_map_jacobian f n)) a /\
    is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
      (riemannian_coarea_fibre_integral f hpFibre u) a.
Proof.
move=> hnm hLip [b hu].
pose X := [the choiceType of riemannian_metric_space hg].
pose mu := riemannian_hausdorff_measure hg m%:R hpSource.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hpSource.
pose U := @PartialFunctionExtension.value X (extended_real_line R) u 0.
have hExt : is_partial_function_total_extension u U := @PartialFunctionExtension.laws X _ u 0.
have hEqual : measure_almost_equal mu u (partial_function_total U).
  apply:(@measure_almost_everywhere_mono R X mu hMu _ _ _
    (measurable_function_domain hu.1))=> x [j hj].
  exists j; split; first exact hj; exact:hExt x j hj.
have hU := measure_integral_almost_equal hMu hu hEqual.
have [a [hLeft hRight]] := @riemannian_coarea_signed_total_integral R m n A B g h hg hh f
  hpSource hpTarget hpFibre U hnm hLip (ex_intro _ b hU).
exists a; split.
- apply:(measure_integral_almost_equal hMu hLeft).
  apply:(partial_density_product_almost_equal hMu (measure_almost_equal_sym hEqual)).
  exact:((measure_almost_equal_self _ _).2 (measurable_function_domain
    (@riemannian_coarea_jacobian_volume_measurable R m n A B g h hg hh f hpSource hLip))).
- exact:(@riemannian_coarea_fibre_integral_null_change R m n A B g h hg hh f
    hpSource hpTarget hpFibre _ _ a (ltnW hnm) hLip (measure_almost_equal_sym hEqual) hRight).
Qed.

(** Source for [federer_3_2_46_coarea]: the printed
    real-weight coarea assertion in 3.2.46, p. 282,
    extending 3.2.12, pp. 249–250. The
    original integrable weight and actual original
    Riemannian Jacobian, volume and complementary
    fibre measures occur in both genuine integrals.
    No auxiliary coordinate, differential field or
    independent inner-integrability hypothesis is supplied. *)
Theorem federer_3_2_46_coarea (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : (0<=m%:R :> R)%R) (hpTarget : (0<=n%:R :> R)%R)
    (hpFibre : (0<=(m-n)%:R :> R)%R)
    (w : riemannian_metric_space hg -> R) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  is_measure_integrable (riemannian_hausdorff_measure hg m%:R hpSource) (real_total_integrand w) ->
  exists a, is_measure_integral (riemannian_hausdorff_measure hg m%:R hpSource)
      (partial_density_product (real_total_integrand w) (extended_riemannian_map_jacobian f n)) a /\
    is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
      (riemannian_coarea_fibre_integral f hpFibre (real_total_integrand w)) a.
Proof. exact:riemannian_weighted_coarea_formula. Qed.
