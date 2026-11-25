(** Federer (1969), 4.1.9, p. 364: evaluate the
    exact original time moment before integrating over U.
    The original nonnegative Fubini theorem includes
    infinite spatial integrals. The pointwise time moment
    remains finite, including both zero endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology normedtype realfun.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentDomain CurrentDomainRadonSigmaFinite
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  CurrentCartesianDomainRadonProduct MetricSubsetBackground MetricProductBackground
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  ProductMeasure RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP CompactSupportSummability
  RealMetricBackground LebesgueScalarMeasure SummableRealFunctionUP ScalarAffinePowerMeanBounds HomotopyAffinePowerFields ScalarAffinePowerMoment
  CurrentHomotopyTimeScalarIntegral CurrentHomotopyTimePartialIntegral
  RealSubsetIntegralAgreement SummableRealArithmetic PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  PartialFunctionPrecomposition PartialFunctionSourceImage PartialProductSections ParameterizedIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  MeasureIntegralBounds MeasureIntegralComparison MeasureNonnegativeIntegral MeasureSubsetIntegral
  CountablyMeasurableNullModification CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableProduct
  ProductFunctionFubini TotalNonnegativeProductIntegral MeasureAlmostEquality MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HomotopyAffinePowerFubini.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation TT := (current_domain R 1%N AT).
Local Notation UT := (current_domain R n U).
Local Notation PT := [the topologicalType of (TT*UT)%type].
Local Notation S := (@current_homotopy_time_segment R A hA h2).
Local Notation hS := (@current_homotopy_time_representable R h2 A hA).
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N AT hAT S hS).
Local Notation baseS := (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 1%N 1%N AT hAT S hS)).
Local Notation hAlpha := (distribution_representation_measure baseS).
Local Notation hARadon := (distribution_representation_radon baseS).
Local Notation q := (fun t:TT=>@euclidean_one_project R (set_val t)).
Variables a b c:UT->R.
Hypothesis ha:forall x,0<=a x.
Hypothesis hb:forall x,0<=b x.
Hypothesis hc:forall x,0<=c x.
Hypothesis hAContinuous:continuous (a:UT->real_line_metric R).
Hypothesis hBContinuous:continuous (b:UT->real_line_metric R).
Hypothesis hCContinuous:continuous (c:UT->real_line_metric R).


Local Notation E := (@homotopy_affine_power_envelope R n j A U a b c).
Local Notation Mean := (@homotopy_affine_power_mean R n j U a b c).
Local Notation Max := (@homotopy_affine_power_maximum R n j U a b c).
Variable beta:set UT->\bar R.
Hypothesis hBeta:is_measure beta.
Hypothesis hBRadon:is_radon_measure beta.
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation Joint := (real_total_integrand E).
Local Notation Value := (measure_lower_integral mu Joint).
Local Notation Spatial t := (real_total_integrand (fun x:UT=>a x*((1-t)*b x+t*c x)^+j)).
Local Notation Outer := (parameterized_integral beta (fun t=>Spatial t)).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [homotopy_affine_fixed_point_time_moment]:
    the literal original time integral at each original
    spatial point has exactly the printed finite mean,
    supporting the middle equality in Federer 4.1.9,
    p. 364. There is no exceptional spatial point. *)
Lemma homotopy_affine_fixed_point_time_moment (x:UT):
  is_measure_integral alpha (real_total_integrand (fun t:TT=>E (t,x))) (Mean x)%:E.
Proof.
pose F t:=(`|1-t|*b x+`|t|*c x)^+j.
have hMoment:=@scalar_affine_power_moment R (b x) (c x) j.
have hAbsMoment:is_measure_subset_integral (@lebesgue_scalar_measure R) I
    (real_total_integrand F) ((\sum_(k<j.+1) b x^+k*c x^+(j-k))/j.+1%:R)%:E.
  apply:(@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R) I
    (fun t=>((1-t)*b x+t*c x)^+j) F _ _ hMoment)=>t /andP[ht0 ht1].
  by rewrite /F (ger0_norm ht0) ger0_norm // subr_ge0.
have hTime:=(@current_homotopy_time_scalar_integral_iff R h2 A hA (real_total_integrand F) _).2 hAbsMoment.
have hRealTime:is_measure_integral alpha (real_total_integrand (fun t:TT=>F (q t)))
    ((\sum_(k<j.+1) b x^+k*c x^+(j-k))/j.+1%:R)%:E.
  apply:(@measure_integral_graph_equivalent R TT alpha _ _ _ _ hTime)=>t z.
  by rewrite !real_total_integrand_graph.
exact:(@real_total_integral_scale R TT alpha hAlpha (fun t:TT=>F (q t))
  ((\sum_(k<j.+1) b x^+k*c x^+(j-k))/j.+1%:R) (a x) hRealTime).
Qed.

(** Source for [homotopy_affine_spatial_integral]: the
    original spatial scalar integrand has an actual
    nonnegative integral at every t in [0,1],
    supporting the first affine estimate in Federer
    4.1.9, p. 364. The integral may be infinite. *)
Theorem homotopy_affine_spatial_integral t:0<=t<=1->
  is_measure_integral beta (Spatial t) (measure_lower_integral beta (Spatial t)).
Proof.
move=>/andP[ht0 ht1].
have hComplement:0<=1-t by rewrite subr_ge0.
have hPower:continuous (fun s:R=>s^+j) by move=>s;exact:exprn_continuous.
have hContinuous:continuous (fun x:UT=>(a x*((1-t)*b x+t*c x)^+j:real_line_metric R)).
  move=>x.
  have hBase:(fun x:UT=>(1-t)*b x+t*c x) @ (nbhs x) --> (1-t)*b x+t*c x.
    exact:cvgD (cvgM (cvg_cst _) (@hBContinuous x)) (cvgM (cvg_cst _) (@hCContinuous x)).
  have hPow:(fun y:UT=>((1-t)*b y+t*c y)^+j) @ (nbhs x) --> ((1-t)*b x+t*c x)^+j.
    exact:(continuous_comp hBase (hPower _)).
  exact:(cvgM (@hAContinuous x) hPow).
have hMeas:=@continuous_real_integrand_measurable R UT beta hBeta
  (fun B hB=>borel_regular_borel_measurable hBeta (radon_borel_regular hBeta hBRadon) hB)
  (fun x:UT=>a x*((1-t)*b x+t*c x)^+j) hContinuous.
have hPositive:measure_almost_everywhere beta (partial_extended_nonnegative_locus (Spatial t)).
  apply:(@measure_almost_everywhere_mono R UT beta hBeta setT _ _ (measure_almost_everywhere_true hBeta))=>x _.
  exists (a x*((1-t)*b x+t*c x)^+j)%:E;split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;apply:mulr_ge0;first exact:ha.
  apply:exprn_ge0;exact:addr_ge0 (mulr_ge0 hComplement (hb x)) (mulr_ge0 ht0 (hc x)).
exact:(@nonnegative_measurable_function_integral R UT beta hBeta (Spatial t) hMeas hPositive).1.
Qed.

(** Source for [homotopy_affine_joint_integral]: the exact
    nonnegative product envelope has its actual integral,
    supporting Federer 4.1.9, p. 364, by 2.4.4(2),
    p. 82. The value may be positive infinity. *)
Lemma homotopy_affine_joint_integral:is_measure_integral mu Joint Value.
Proof.
have hMeas:=@homotopy_affine_power_envelope_measurable R h2 n j A hA U hU a b c
  hAContinuous hBContinuous hCContinuous beta hBeta hBRadon.
have hPositive:measure_almost_everywhere mu (partial_extended_nonnegative_locus Joint).
  apply:(@measure_almost_everywhere_mono R (Choice.clone (TT*UT)%type _) mu hm setT _ _
    (measure_almost_everywhere_true hm))=>z _.
  exists (E z)%:E;split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;exact:(@homotopy_affine_power_envelope_nonnegative R n j A U a b c ha hb hc z).
exact:(@nonnegative_measurable_function_integral R (Choice.clone (TT*UT)%type _) mu hm Joint hMeas hPositive).1.
Qed.

(** Source for [homotopy_affine_product_countably_measurable]:
    the original Radon product satisfies the countable
    hypotheses of 2.6.2, supporting the exact affine
    mass equality in Federer 4.1.9, p. 364.
    Neither factor needs finite total mass. *)
Lemma homotopy_affine_product_countably_measurable:measure_countably_measurable mu setT.
Proof.
exact:(@product_whole_countably_measurable R TT UT alpha beta hAlpha hBeta
  (@current_domain_radon_countably_measurable R 1%N AT hAT alpha hAlpha hARadon)
  (@current_domain_radon_countably_measurable R n U hU beta hBeta hBRadon)).
Qed.

(** Source for [homotopy_affine_mean_integral]: the exact
    original finite time moment integrates over the
    original spatial variation to the product value,
    supporting the equality in Federer 4.1.9, p. 364.
    An infinite spatial integral remains permitted. *)
Theorem homotopy_affine_mean_integral:is_measure_integral beta (real_total_integrand Mean) Value.
Proof.
have hCount:=countably_measurable_function_on_countable_source hm
  (@CountablyMeasurableNullModification.extended_real_zero_closed R)
  homotopy_affine_product_countably_measurable homotopy_affine_joint_integral.1.
have hSpatial:=(@product_function_fubini R TT UT alpha beta hAlpha hBeta Joint Value
  homotopy_affine_joint_integral hCount).2.
apply:(@measure_integral_graph_equivalent R UT beta _ _ Value _ hSpatial)=>x w.
rewrite parameterized_integral_specification real_total_integrand_graph.
have hMoment:is_measure_integral alpha (partial_product_horizontal_section Joint x) (Mean x)%:E.
  apply:(@measure_integral_graph_equivalent R TT alpha _ _ _ _
    (homotopy_affine_fixed_point_time_moment x))=>t z.
  change (partial_function_graph (real_total_integrand (fun t:TT=>E (t,x))) t z<->
    partial_function_graph Joint (t,x) z).
  by rewrite !real_total_integrand_graph.
split;first by move=>hIntegral;exact:esym (measure_integral_unique hIntegral hMoment).
by move=> <-.
Qed.

(** Source for [homotopy_affine_literal_time_integral]: the
    time-then-space integral is exactly the original
    [0,1] integral of the original spatial scalar
    integrals, supporting Federer 4.1.9, p. 364.
    The spatial integrals retain their partial domain. *)
Theorem homotopy_affine_literal_time_integral:
  is_measure_subset_integral (@lebesgue_scalar_measure R) I Outer Value.
Proof.
have hCount:=countably_measurable_function_on_countable_source hm
  (@CountablyMeasurableNullModification.extended_real_zero_closed R)
  homotopy_affine_product_countably_measurable homotopy_affine_joint_integral.1.
have hOuter:=(@product_function_fubini R TT UT alpha beta hAlpha hBeta Joint Value
  homotopy_affine_joint_integral hCount).1.
pose Inner:=parameterized_integral beta (partial_product_vertical_section Joint).
have hGood:=@measure_almost_everywhere_and R TT alpha hAlpha _ _
  (@current_homotopy_time_band_conull R h2 A hA) (measurable_function_domain hOuter.1).
have hAgreement:measure_almost_equal alpha Inner (partial_function_precompose q Outer).
  apply:(@measure_almost_everywhere_mono R TT alpha hAlpha _ _ _ hGood)=>t [ht [v hv]].
  exists v;split;first exact:hv.
  apply:(parameterized_integral_specification beta (fun t=>Spatial t) (q t) v).2.
  have hSection:=(parameterized_integral_specification beta (partial_product_vertical_section Joint) t v).1 hv.
  apply:(@measure_integral_graph_equivalent R UT beta _ _ v _ hSection)=>x w.
  change (partial_function_graph (real_total_integrand (fun x:UT=>E (t,x))) x w<->
    partial_function_graph (Spatial (q t)) x w).
  rewrite !real_total_integrand_graph.
  by rewrite (@homotopy_affine_power_envelope_value R n j A U a b c t x ht).
have hActual:=@measure_integral_almost_equal R TT alpha hAlpha _ _ Value hOuter hAgreement.
exact:(@current_homotopy_time_scalar_integral_iff R h2 A hA Outer Value).1 hActual.
Qed.

(** Source for [homotopy_affine_maximum_integral]: the last
    original scalar bound has a nonnegative actual
    integral, supporting the final inequality in Federer
    4.1.9, p. 364. Infinite values are included. *)
Theorem homotopy_affine_maximum_integral:
  is_measure_integral beta (real_total_integrand Max)
    (measure_lower_integral beta (real_total_integrand Max)).
Proof.
have hMeas:=@homotopy_affine_power_maximum_measurable R n j U a b c
  hAContinuous hBContinuous hCContinuous beta hBeta hBRadon.
have hPositive:measure_almost_everywhere beta (partial_extended_nonnegative_locus (real_total_integrand Max)).
  apply:(@measure_almost_everywhere_mono R UT beta hBeta setT _ _ (measure_almost_everywhere_true hBeta))=>x _.
  exists (Max x)%:E;split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin.
  exact:le_trans (andP (@homotopy_affine_power_mean_maximum_bound R n j U a b c ha hb hc x)).1
    (andP (@homotopy_affine_power_mean_maximum_bound R n j U a b c ha hb hc x)).2.
exact:(@nonnegative_measurable_function_integral R UT beta hBeta (real_total_integrand Max) hMeas hPositive).1.
Qed.

(** Source for [homotopy_affine_mean_integral_maximum_bound]:
    the integrated exact original mean is at most
    the integrated original endpoint maximum, supporting
    the last inequality in Federer 4.1.9, p. 364. *)
Theorem homotopy_affine_mean_integral_maximum_bound:
  (Value<=measure_lower_integral beta (real_total_integrand Max))%E.
Proof.
apply:(@measure_integral_monotone R UT beta hBeta _ _ _ _
  homotopy_affine_mean_integral homotopy_affine_maximum_integral).
apply:(@measure_almost_everywhere_mono R UT beta hBeta setT _ _ (measure_almost_everywhere_true hBeta))=>x _.
exists (Mean x)%:E,(Max x)%:E;split;first by rewrite real_total_integrand_graph.
split;first by rewrite real_total_integrand_graph.
rewrite lee_fin;exact:(andP (@homotopy_affine_power_mean_maximum_bound R n j U a b c ha hb hc x)).2.
Qed.
End HomotopyAffinePowerFubini.
