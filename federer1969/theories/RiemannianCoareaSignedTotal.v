(** Federer (1969), 3.2.46, p. 282, extending 3.2.12, pp. 249–250: extend the
    characteristic-expansion formula by positive and negative
    parts, using 2.4.4(6), as in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianPathLipschitz RiemannianMapJacobian RiemannianJacobianDensityMeasure
  RiemannianCoareaJacobianMeasurable RiemannianCoareaJacobianUniformBound
  RiemannianNonnegativeWeightedCoarea RiemannianCoareaFibreIntegral RiemannianCoareaFibreIntegralParts
  ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart PartialExtendedArithmetic PartialDensityProduct
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureIntegralPartsExist MeasureIntegralPartsDifference MeasureIntegralNegationLaw MeasureIntegralAddition
  MeasureChangeOfDensity NonnegativeExtendedNormOrder NumericalSum BoundedDensityIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_coarea_signed_total_integral]: the actual-metric extension in 3.2.46, p. 282, of Federer
    3.2.12, pp. 249–250, for total integrable functions.
    The integral may have either infinite value. The finite
    variation is preserved by the actual bounded Jacobian,
    so both signed differences are proved to be defined. *)
Theorem riemannian_coarea_signed_total_integral (R:realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : (0<=m%:R :> R)%R) (hpTarget : (0<=n%:R :> R)%R)
    (hpFibre : (0<=(m-n)%:R :> R)%R)
    (u : riemannian_metric_space hg -> extended_real_line R) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  is_measure_integrable (riemannian_hausdorff_measure hg m%:R hpSource) (partial_function_total u) ->
  exists a, is_measure_integral (riemannian_hausdorff_measure hg m%:R hpSource)
      (partial_density_product (partial_function_total u) (extended_riemannian_map_jacobian f n)) a /\
    is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
      (riemannian_coarea_fibre_integral f hpFibre (partial_function_total u)) a.
Proof.
move=>hnm hLip [a ha].
pose mu:=riemannian_hausdorff_measure hg m%:R hpSource.
pose nu:=riemannian_jacobian_measure f hpSource n.
pose beta:=riemannian_hausdorff_measure hh n%:R hpTarget.
have hm:=@riemannian_hausdorff_is_measure R m A g hg m%:R hpSource.
have hn:=@riemannian_jacobian_measure_is_measure R m n A B g h hg hh f hpSource n hLip.
have hb:=@riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have hPost (phi:extended_real_line R->extended_real_line R) x j:
    partial_function_graph (partial_function_postcompose (partial_function_total u) phi) x j <->
    partial_function_graph (partial_function_total (fun x=>phi (u x))) x j.
  split.
  - move=>[v [hv <-]]; by rewrite -(hv:u x=v).
  - move=>hj; exists (u x); by split.
have [P [N [hp [hneg [hP hN]]]]]:=@measurable_function_parts_integrals R _ mu hm _ ha.1.
have [z hz]:=integrable_function_part_difference_defined hm ha hp hneg hP hN.
have hpT:=measure_integral_graph_equivalent (hPost (@extended_positive_part R)) hp.
have hnT:=measure_integral_graph_equivalent (hPost (@extended_negative_part R)) hneg.
have [P' [hpNu hpBeta]]:=@riemannian_nonnegative_weighted_coarea R m n A B g h hg hh f
  hpSource hpTarget hpFibre _ hnm hLip hpT.1
  (fun x=>extended_positive_part_nonnegative (u x)).
have [N' [hnNu hnBeta]]:=@riemannian_nonnegative_weighted_coarea R m n A B g h hg hh f
  hpSource hpTarget hpFibre _ hnm hLip hnT.1
  (fun x=>extended_negative_part_nonnegative (u x)).
have hP':0<=P':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_positive_part_nonnegative (u x)) hpNu.
have hN':0<=N':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_negative_part_nonnegative (u x)) hnNu.
have [C [hC hBound]]:=@riemannian_coarea_jacobian_uniform_bound R m n A B g h hg hh f hLip.
have hDensity:=riemannian_jacobian_measure_laws f hpSource n.
have hMeas:=@riemannian_coarea_jacobian_volume_measurable R m n A B g h hg hh f hpSource hLip.
have hPos:=@riemannian_jacobian_degree_nonnegative_almost R m n A B g h hg hh f hpSource n hLip.

have hPBound:=bounded_density_integral_comparison hm hDensity hMeas hPos hC hBound
  (fun x=>extended_positive_part_nonnegative (u x)) hpT hpNu.
have hNBound:=bounded_density_integral_comparison hm hDensity hMeas hPos hC hBound
  (fun x=>extended_negative_part_nonnegative (u x)) hnT hnNu.
have hFinite (b : \bar R):0<=b -> b< +oo -> C%:E*b< +oo.
  move=>hb0 hbFin.
  have hbNum:b \is a fin_num by rewrite (ge0_fin_numE hb0) hbFin.
  by rewrite -(fineK hbNum) -EFinM ltry.
have hOne:(P'< +oo)||(N'< +oo).
  have /orP[hPF|hNF]:=(nonnegative_difference_defined hP hN).1 (ex_intro _ z hz).
  - apply/orP; left; exact (le_lt_trans hPBound (hFinite P hP hPF)).
  - apply/orP; right; exact (le_lt_trans hNBound (hFinite N hN hNF)).
have [b hDiff]:=(nonnegative_difference_defined hP' hN').2 hOne.
have hpPart:is_measure_integral nu (partial_extended_function_positive_part (partial_function_total u)) P'.
  exact (measure_integral_graph_equivalent (fun x j=>iff_sym (hPost (@extended_positive_part R) x j)) hpNu).
have hnPart:is_measure_integral nu (partial_extended_function_negative_part (partial_function_total u)) N'.
  exact (measure_integral_graph_equivalent (fun x j=>iff_sym (hPost (@extended_negative_part R) x j)) hnNu).
have hSigned:=measure_integral_from_parts hn hpPart hnPart hDiff.
exists b; split.
- exact ((@measure_density_integral_iff R _ mu nu hm (extended_riemannian_map_jacobian f n)
    (partial_function_total u) hDensity hMeas hPos ha.1 b).1 hSigned).
- have hPGraph:=riemannian_coarea_fibre_integral_graph_equivalent f hpFibre
    (fun x j=>iff_sym (hPost (@extended_positive_part R) x j)).
  have hNGraph:=riemannian_coarea_fibre_integral_graph_equivalent f hpFibre
    (fun x j=>iff_sym (hPost (@extended_negative_part R) x j)).
  have hPositiveFibre:=measure_integral_graph_equivalent hPGraph hpBeta.
  have hNegativeFibre:=measure_integral_graph_equivalent hNGraph hnBeta.
  exact (riemannian_coarea_fibre_integral_parts hb hPositiveFibre hNegativeFibre hDiff).
Qed.
