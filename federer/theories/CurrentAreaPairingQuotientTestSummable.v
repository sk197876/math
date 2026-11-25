(** Federer (1969), 4.1.25, p. 383: the actual
    compact target test supplies a bounded variable
    covector. Its quotient is dominated by that bound
    times the original field's integrable mass. All
    analytic hypotheses are derived from the original
    Lipschitz map, Omega field and target test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric ExteriorGrading AlternatingForms
  CurrentSpaces CurrentCoefficientNorms CompactSummableMultivectors
  CompactSummableMultivectorAmbient EuclideanLebesgueDimensions LipschitzUP Rademacher
  PartialFunctionUP PartialAbsolutePartsGraph PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureAbsoluteSummability SummableRealFunctionUP SummableRealArithmetic
  CurrentLipschitzLebesgueActionIntegrand CurrentLipschitzLebesgueAction
  CurrentLipschitzLebesgueActionTestBound CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientLaws CurrentAreaPairingQuotientTestSealed
  CurrentAreaPairingQuotientTestLaws CurrentAreaPairingQuotientTestMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TargetTestAreaSummability.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX:=(fun _:X=>True).
Local Notation FullY:=(fun _:Y=>True).
Local Notation hFullX:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hFullY:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation mu:=(@euclidean_lebesgue_measure R m).
Local Notation hm:=(euclidean_lebesgue_is_measure R m).
Local Notation M:=(@current_vector_mass R h2 m m).
Variable f:inner_metric_space (@euclidean_inner_productP R m)->
  inner_metric_space (@euclidean_inner_productP R n).
Hypothesis hLip:is_metric_lipschitz setT f.
Variable xi:@compact_summable_multivector_space R h2 m m FullX hFullX.
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 m m FullX hFullX xi).
Variable psi:@current_test_space R h2 n FullY hFullY m.
Local Notation phi:=(@current_test_value R h2 n FullY hFullY m psi).
Local Notation q:=(@CurrentAreaPairingQuotientTest.value R m n f raw phi).

(** Source for [current_area_pairing_quotient_test_numerator_summable]:
    the actual first displayed action of 4.1.25,
    p. 383, supplies the finite numerator integral
    for every original compact target test. *)
Theorem current_area_pairing_quotient_test_numerator_summable:
  is_measure_summable mu
    (@current_lipschitz_lebesgue_action_integrand R m n m f raw phi).
Proof.
have hNormLip:@is_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f.
  have [L [hL hBound]]:=hLip.
  exists L; split; [exact: hL | exact: hBound].
have hAction:=@current_lipschitz_lebesgue_action R h2 m n m xi f hNormLip psi.
eexists;exact:hAction.
Qed.

(** Source for [current_area_pairing_quotient_test_summable]:
    summability of the variable-test quotient in the
    area proof of 4.1.25, p. 383. No
    summability premise on the test or on its
    source-dependent pairing is added. *)
Theorem current_area_pairing_quotient_test_summable:
  is_measure_summable mu q.
Proof.
have [b hNumerator]:=current_area_pairing_quotient_test_numerator_summable.
have hMeasurable:=@current_area_pairing_quotient_test_measurable R m n f raw phi
  hLip hNumerator.1.
have [B [hB hTestBound]]:=@current_lipschitz_lebesgue_action_test_bound R h2 n m psi.
pose H:=real_total_integrand (fun x:X=>B*M (raw x)).
have hH:is_measure_summable mu H.
  exists (B*@compact_summable_multivector_size R h2 m m FullX hFullX xi).
  exact:(@real_total_integral_scale R X mu hm (fun x=>M (raw x))
    (@compact_summable_multivector_size R h2 m m FullX hFullX xi) B
    (@compact_summable_multivector_ambient_integral R h2 m m FullX hFullX xi)).
have hDifferentiable:=@federer_3_1_6 R m n f hLip.
have hBound:measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value q) H).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDifferentiable)=>x [D hD].
  pose r:=@current_area_pairing_quotient_coefficient R m n raw (phi (f x)) x D.
  exists (`|r|)%:E,(B*M (raw x))%:E.
  split.
  - exists r%:E;split.
    + exact:(@current_area_pairing_quotient_test_at_differential R m n f raw phi x D hD).
    + by rewrite abse_EFin.
  - split;first by apply/real_total_integrand_graph.
    rewrite lee_fin.
    apply:(le_trans (@current_area_pairing_quotient_coefficient_bound
      R m n f raw (phi (f x)) h2 x D hD)).
    rewrite [B*M (raw x)]mulrC.
    apply:ler_wpM2l;last exact:hTestBound (f x).
    exact:(@real_seminorm_nonnegative R (exterior_power X m) M
      (@current_vector_mass_real_norm R h2 m m).1 (raw x)).
exact:(@measure_dominated_summable R X mu hm q H hMeasurable hH hBound).1.
Qed.
End TargetTestAreaSummability.
