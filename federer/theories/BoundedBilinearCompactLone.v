(** Federer (1969), 4.1.7, p. 359:
    a bounded Baire form multiplied by
    a genuine test belongs to the
    weighted target L1 space. This supporting
    norm estimate applies the earlier measurable
    bilinear operations and the finite compact
    norm integral of 4.1.5, p. 350. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  NormBoundedBilinearUP VectorDaniellHypotheses VectorDaniellRationalSpan MeasurableBoundedBilinearProduct
  CompactContinuousVectorFields CompactContinuousVectorMeasurable FunctionLatticeUP CompactSupportFunctionUP
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  MeasureStepIntegralIdentification RadonCompactScalarIntegral SummableRealFunctionUP SummableRealArithmetic
  MeasureIntegralUP VectorDaniellPairingMeasurability SeparableVectorLone MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bounded_bilinear_compact_lone]:
    the original product of a bounded
    measurable field and a compact continuous
    field is L1 for every Radon
    measure, supporting the Baire projection
    in Federer 4.1.7, p. 359.
    The measure may have infinite total mass. *)
Theorem bounded_bilinear_compact_lone (R:realType) (X:topologicalType)
    (A B C:lmodType R) (NA:A->R) (NB:B->R) (NC:C->R)
    (hNA:is_real_norm NA) (hNB:is_real_norm NB) (hNC:is_real_norm NC)
    (hSepA:is_separable_normed_space hNA) (hSepB:is_separable_normed_space hNB)
    (hSepC:is_separable_normed_space hNC)
    (F:A->B->C) (hF:norm_bounded_bilinear NA NB NC F)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (a:X->A) (b:X->B) (M:R):
  is_measure_measurable_function mu (partial_function_total (fun x=>(a x:real_norm_metric_space hNA)))->
  0<=M->(forall x,NA (a x)<=M)->compact_continuous_vector_fields hNB b->
  is_measure_lp_function mu 1
    (partial_function_total (fun x=>(F (a x) (b x):real_norm_metric_space hNC))).
Proof.
move=>hA hM hBound hB.
have hBMeas:=@compact_continuous_vector_measurable R X B NB hNB mu hm hr b hB.
have hProduct:=@measurable_bounded_bilinear_product R X A B C NA NB NC hNA hNB hNC
  mu hm F hF a b hSepA hSepB hA hBMeas.
have hNorm:=@measurable_total_borel_postcomposition R X (real_norm_metric_space hNC)
  (real_line_metric R) mu hm (fun x=>(F (a x) (b x):real_norm_metric_space hNC)) (fun z=>NC z)
  hProduct (continuous_borel_function (@real_norm_metric_norm_continuous R C NC hNC)).
have hNormMeas:=@measurable_partial_real_embedding R X mu hm _ hNorm.
have hNormB:positive_function_lattice (@compactly_supported_continuous_functions R X) (fun x=>NB (b x)).
  split;first exact:(@compact_continuous_vector_field_norm R X B NB hNB b hB).
  move=>x;exact:real_seminorm_nonnegative hNB.1 _.
pose I:=@radon_positive_compact_integral R X mu hm hr.
have hIntegral:=@radon_positive_compact_integral_laws R X mu hm hr _ hNormB.
have [K [hK hEstimate]]:=hF.2.
have hScaled:=@real_total_integral_scale R X mu hm (fun x=>NB (b x))
  (I (fun x=>NB (b x))) (K*M) hIntegral.
have hDom x:`|NC (F (a x) (b x))|<=(K*M)*NB (b x).
  rewrite (ger0_norm (real_seminorm_nonnegative hNC.1 _)).
  apply:(le_trans (hEstimate (a x) (b x))).
  rewrite mulrA.
  exact:(ler_wpM2r (real_seminorm_nonnegative hNB.1 (b x)) (ler_wpM2l hK (hBound x))).
have [c [hValue _]]:=@real_total_dominated_integral R X mu hm
  (fun x=>NC (F (a x) (b x))) (fun x=>(K*M)*NB (b x))
  ((K*M)*I (fun x=>NB (b x))) hNormMeas hScaled hDom.
have [D hD]:=rational_dense_subspace_exists hSepC.
exact:(@separable_vector_summable_norm_lone R X C NC hNC D hD mu hm
  (fun x=>(F (a x) (b x):real_norm_metric_space hNC)) c hProduct hValue).
Qed.
