(** Federer (1969), 4.1.25, p. 383: the
    weighted area formula identifies each covector pairing
    of the original vector fibre sum with the original
    exterior-image numerator integral. The scalar auxiliary
    is conull and summable, while the original vector
    summand keeps its nonzero-Jacobian domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness ExteriorGrading AlternatingForms
  PartialFunctionUP PartialFibreNumericalSum PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  MeasurableFunctionUP SummableRealFunctionUP EuclideanLebesgueDimensions
  HausdorffMeasure LipschitzUP AreaWeightedFormula
  EuclideanJacobianMeasurable
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  CurrentLipschitzLebesgueActionIntegrand CurrentAreaNormalisedImageSealed
  CurrentAreaFibreSumUP CurrentAreaGoodFibres
  CurrentAreaPairingQuotientSealed CurrentAreaPairingQuotientNumerator
  CurrentAreaPairingQuotientProduct CurrentAreaPairingQuotientSummable
  CurrentAreaPairingQuotientFibreGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_pairing_quotient_area_integrals]:
    the fixed-covector integral equality for the original
    full-fibre vector sum in 4.1.25, p. 383.
    All actual scalar fibre sums and both finite
    integral values are derived; no summability or
    domain premise on the target fibre is added. *)
Theorem current_area_pairing_quotient_area_integrals (R:realType)
    (h2:(1+1:R)!=0) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (hLip:is_metric_lipschitz setT f)
    (xi:@compact_summable_multivector_space R h2 m m (fun _=>True)
      (fun (x:R_n R m) (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R m)) x))
    (a:A_m (R_n R n) R^o m) :
  let hFull:=fun (x:R_n R m) (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R m)) x in
  let raw:=@compact_summable_multivector_ambient_value R h2 m m (fun _=>True) hFull xi in
  exists b:R,
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (@current_lipschitz_lebesgue_action_integrand R m n m f raw (fun _=>a)) b%:E /\
    is_measure_integral
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_fibre_numerical_sum f
        (@current_area_fibre_pairing_integrand R (R_n R m) n m
          (@CurrentAreaNormalisedImage.value R m n f raw) a)) b%:E.
Proof.
move=>hFull raw.
pose X:=R_n R m.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose H:=@hausdorff_measure R Y m.
pose hH:=@hausdorff_measure_is_measure R Y m.
pose q:=@CurrentAreaPairingQuotient.value R m n f raw a.
pose original:=@current_area_fibre_pairing_integrand R X n m
  (@CurrentAreaNormalisedImage.value R m n f raw) a.
have [b hNumerator]:=@current_area_pairing_numerator_summable R h2 m n f hLip xi a.
have hSummable:=@current_area_pairing_quotient_summable R h2 m n f hLip xi a.
have [c [hSource hTarget]]:=@euclidean_weighted_area_formula R m n f q hLip
  (measure_summable_integrable hSummable).
have hProduct:is_measure_integral mu
    (partial_density_product q (extended_euclidean_jacobian f)) b%:E.
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hNumerator)=>x z.
  symmetry;exact:(@current_area_pairing_quotient_product_graph R h2 m n f raw a x z).
have hValue:c=b%:E:=measure_integral_unique hSource hProduct.
rewrite hValue in hTarget.
exists b;split;first exact:hNumerator.
apply:(@measure_integral_almost_equal R Y H hH _ _ b%:E hTarget).
have hGood:=@current_area_good_fibres R m n f raw hLip.
have hBoth:=measure_almost_everywhere_and hH hGood (measurable_function_domain hTarget.1).
apply:(@measure_almost_everywhere_mono R Y H hH _ _ _ hBoth)=>y [hy [v hV]].
exists v;split;first exact:hV.
exact:(@current_area_pairing_quotient_fibre_graph R m n f raw a y v hy).1 hV.
Qed.
