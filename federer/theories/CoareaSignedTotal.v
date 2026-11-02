(** Federer (1969), 3.2.12, pp. 249–250: extend the
    characteristic-expansion formula by positive and negative
    parts, using 2.4.4(6), as in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart PartialExtendedArithmetic PartialDensityProduct MeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralPartsExist MeasureIntegralPartsDifference
  MeasureIntegralNegationLaw MeasureIntegralAddition MeasureChangeOfDensity NonnegativeExtendedNormOrder
  NumericalSum LipschitzUP HausdorffMeasure
  EuclideanTargetJacobianMeasurable EuclideanTargetJacobianUpperBound CoareaJacobianMeasure
  CoareaNonnegativeWeighted CoareaFibreIntegral CoareaFibreIntegralParts BoundedDensityIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_signed_total_integral]: Federer
    3.2.12, pp. 249–250, for total integrable functions.
    The integral may have either infinite value. The finite
    variation is preserved by the actual bounded Jacobian,
    so both signed differences are proved to be defined. *)
Theorem coarea_signed_total_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u:R_n R m->extended_real_line R):
  (n<m)%N ->is_metric_lipschitz setT f ->
  is_measure_integrable (@euclidean_lebesgue_measure R m) (partial_function_total u) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_density_product (partial_function_total u) (extended_euclidean_target_jacobian f)) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (coarea_fibre_integral f (partial_function_total u)) a.
Proof.
move=>hnm hLip [a ha].
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_coarea_measure f.
pose beta:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R m.
have hn:=euclidean_coarea_measure_is_measure hLip.
have hb:=euclidean_lebesgue_is_measure R n.
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
have [P' [hpNu hpBeta]]:=coarea_nonnegative_weighted_integral hnm hLip hpT.1
  (fun x=>extended_positive_part_nonnegative (u x)).
have [N' [hnNu hnBeta]]:=coarea_nonnegative_weighted_integral hnm hLip hnT.1
  (fun x=>extended_negative_part_nonnegative (u x)).
have hP':0<=P':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_positive_part_nonnegative (u x)) hpNu.
have hN':0<=N':=nonnegative_total_integral_value_ge0 hn
  (fun x=>extended_negative_part_nonnegative (u x)) hnNu.
have [M [hM hMBound]]:=hLip.
pose C:=(M^+n)%R.
have hC:(0<C)%R:=exprn_gt0 n hM.
have hDensity:=euclidean_coarea_measure_laws f.
have hMeas:=extended_euclidean_target_jacobian_measurable hLip.
have hPos:=euclidean_coarea_jacobian_nonnegative_almost hLip.
have hBound:forall x j,partial_function_graph (extended_euclidean_target_jacobian f) x j -> j<=C%:E.
  exact (euclidean_target_jacobian_global_upper_bound (ltW hM) hMBound).
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
- exact ((@measure_density_integral_iff R _ mu nu hm (extended_euclidean_target_jacobian f)
    (partial_function_total u) hDensity hMeas hPos ha.1 b).1 hSigned).
- have hPGraph:=coarea_fibre_integral_graph_equivalent f
    (fun x j=>iff_sym (hPost (@extended_positive_part R) x j)).
  have hNGraph:=coarea_fibre_integral_graph_equivalent f
    (fun x j=>iff_sym (hPost (@extended_negative_part R) x j)).
  have hpFibre:=measure_integral_graph_equivalent hPGraph hpBeta.
  have hnFibre:=measure_integral_graph_equivalent hNGraph hnBeta.
  exact (coarea_fibre_integral_parts hb hpFibre hnFibre hDiff).
Qed.
