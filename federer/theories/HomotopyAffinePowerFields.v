(** Federer (1969), 4.1.9, p. 364: the scalar
    fields in the three affine mass estimates. The
    supporting extension uses absolute time coefficients
    outside [0,1] only; on the original interval it
    is exactly the printed integrand. Its original
    spatial factors are arbitrary nonnegative continuous functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology normedtype realfun.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanDistributionMeasureContext InnerMetric IsotropyGroupTopology TopologicalProductMaps CurrentDomain CurrentDomainRadonSigmaFinite
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTimeDensity
  CurrentCartesianDomainRadonProduct MetricSubsetBackground MetricProductBackground
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  ProductMeasure RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP CompactSupportSummability
  RealMetricBackground SummableRealFunctionUP ScalarAffinePowerMeanBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HomotopyAffinePowerFields.
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

(** Source for [homotopy_affine_power_envelope]: the original
    integrand a(x)[(1-t)b(x)+tc(x)]^j on [0,1],
    supporting Federer 4.1.9, p. 364. The absolute
    coefficients give a nonnegative continuous extension
    for the proof on the original open time domain. *)
Definition homotopy_affine_power_envelope (z:TT*UT):R:=
  a z.2*(`|1-q z.1|*b z.2+`|q z.1|*c z.2)^+j.

(** Source for [homotopy_affine_power_mean]: the exact
    original coefficient a(x) sum b(x)^k c(x)^(j-k)/(j+1),
    supporting the middle equality in Federer 4.1.9,
    p. 364. The denominator is always positive. *)
Definition homotopy_affine_power_mean (x:UT):R:=
  a x*((\sum_(k<j.+1) b x^+k*c x^+(j-k))/j.+1%:R).

(** Source for [homotopy_affine_power_maximum]: the original
    last scalar bound a(x) max(b(x)^j,c(x)^j),
    supporting Federer 4.1.9, p. 364. The degree
    zero coefficient is one even at zero endpoints. *)
Definition homotopy_affine_power_maximum (x:UT):R:=a x*Num.max (b x^+j) (c x^+j).

(** Source for [homotopy_affine_power_envelope_value]: on
    the original closed time interval the auxiliary
    extension is exactly Federer's printed integrand,
    supporting 4.1.9, p. 364. *)
Lemma homotopy_affine_power_envelope_value (t:TT) x:
  0<=q t<=1->homotopy_affine_power_envelope (t,x)=a x*((1-q t)*b x+q t*c x)^+j.
Proof.
move=>/andP[ht0 ht1];rewrite /homotopy_affine_power_envelope /=.
by rewrite (ger0_norm ht0) ger0_norm // subr_ge0.
Qed.

(** Source for [homotopy_affine_power_envelope_nonnegative]:
    the supporting envelope is nonnegative, including
    degree zero, for the nonnegative Fubini proof
    of Federer 4.1.9, p. 364. *)
Lemma homotopy_affine_power_envelope_nonnegative z:0<=homotopy_affine_power_envelope z.
Proof.
apply:mulr_ge0;first exact:ha.
apply:exprn_ge0;exact:addr_ge0 (mulr_ge0 (normr_ge0 _) (hb z.2)) (mulr_ge0 (normr_ge0 _) (hc z.2)).
Qed.

(** Source for [homotopy_affine_power_envelope_continuous]:
    the actual auxiliary envelope is jointly continuous
    on the original two domains, supporting the
    Fubini proof in Federer 4.1.9, p. 364. *)
Lemma homotopy_affine_power_envelope_continuous:
  continuous (homotopy_affine_power_envelope:PT->real_line_metric R).
Proof.
have hCoordinate:continuous (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1%N))=>
    (@euclidean_one_project R x:real_line_metric R)).
  move=>x;exact:(continuous_comp (@euclidean_distribution_norm_to_inner R 1%N x)
    (@euclidean_one_project_continuous R x)).
have hQ:continuous (q:TT->real_line_metric R).
  move=>t;exact:(continuous_comp
    (@set_type_val_continuous (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1%N))) AT t)
    (hCoordinate (set_val t))).
have hPower:continuous (fun t:R=>t^+j) by move=>t;exact:exprn_continuous.
move=>z.
have hTime:(fun z:PT=>q z.1) @ (nbhs z) --> q z.1:=continuous_comp (@first_projection_continuous TT UT z) (hQ z.1).
have hFirst:(fun z:PT=>a z.2) @ (nbhs z) --> a z.2:=continuous_comp (@second_projection_continuous TT UT z) (@hAContinuous z.2).
have hB:(fun z:PT=>b z.2) @ (nbhs z) --> b z.2:=continuous_comp (@second_projection_continuous TT UT z) (@hBContinuous z.2).
have hC:(fun z:PT=>c z.2) @ (nbhs z) --> c z.2:=continuous_comp (@second_projection_continuous TT UT z) (@hCContinuous z.2).
have hBase:(fun z:PT=>`|1-q z.1|*b z.2+`|q z.1|*c z.2) @ (nbhs z) -->
    `|1-q z.1|*b z.2+`|q z.1|*c z.2.
  exact:cvgD (cvgM (cvg_norm (cvgB (cvg_cst _) hTime)) hB) (cvgM (cvg_norm hTime) hC).
exact:cvgM hFirst (continuous_comp hBase (hPower _)).
Qed.

Variable beta:set UT->\bar R.
Hypothesis hBeta:is_measure beta.
Hypothesis hBRadon:is_radon_measure beta.
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).

(** Source for [homotopy_affine_power_envelope_measurable]:
    the exact nonnegative envelope is measurable for
    the original product Radon measure, supporting
    the affine mass calculation in Federer 4.1.9,
    p. 364. No finite total mass is imposed. *)
Lemma homotopy_affine_power_envelope_measurable:
  is_measure_measurable_function mu (real_total_integrand homotopy_affine_power_envelope).
Proof.
have hRadon:=@current_domain_radon_product R 1%N n AT U hAT hU alpha beta hAlpha hBeta hARadon hBRadon.
exact:(@continuous_real_integrand_measurable R PT mu hm
  (fun B hB=>borel_regular_borel_measurable hm (radon_borel_regular hm hRadon) hB)
  homotopy_affine_power_envelope homotopy_affine_power_envelope_continuous).
Qed.

(** Source for [homotopy_affine_power_maximum_measurable]:
    the original last scalar bound is measurable,
    supporting its actual integral in Federer 4.1.9,
    p. 364. Values may have an infinite integral. *)
Lemma homotopy_affine_power_maximum_measurable:
  is_measure_measurable_function beta (real_total_integrand homotopy_affine_power_maximum).
Proof.
have hPower:continuous (fun t:R=>t^+j) by move=>t;exact:exprn_continuous.
have hContinuous:continuous (homotopy_affine_power_maximum:UT->real_line_metric R).
  move=>x.
  have hBP:(fun y:UT=>b y^+j) @ (nbhs x) --> b x^+j.
    exact:(continuous_comp (@hBContinuous x) (hPower _)).
  have hCP:(fun y:UT=>c y^+j) @ (nbhs x) --> c x^+j.
    exact:(continuous_comp (@hCContinuous x) (hPower _)).
  have hMax:(fun y:UT=>Num.max (b y^+j) (c y^+j)) @ (nbhs x) -->
      Num.max (b x^+j) (c x^+j):=continuous_max hBP hCP.
  exact:(cvgM (@hAContinuous x) hMax).
exact:(@continuous_real_integrand_measurable R UT beta hBeta
  (fun B hB=>borel_regular_borel_measurable hBeta (radon_borel_regular hBeta hBRadon) hB)
  homotopy_affine_power_maximum hContinuous).
Qed.

(** Source for [homotopy_affine_power_mean_maximum_bound]:
    the exact original mean is nonnegative and bounded
    by the last original scalar factor, supporting
    both affine comparisons in Federer 4.1.9, p. 364. *)
Lemma homotopy_affine_power_mean_maximum_bound x:
  0<=homotopy_affine_power_mean x<=homotopy_affine_power_maximum x.
Proof.
apply/andP;split.
- exact:mulr_ge0 (ha x) (@scalar_affine_power_mean_nonnegative R (b x) (c x) (hb x) (hc x) j).
- rewrite /homotopy_affine_power_mean /homotopy_affine_power_maximum.
  apply:(ler_wpM2l (ha x)).
  exact:(@scalar_affine_power_mean_max_bound R (b x) (c x) (hb x) (hc x) j).
Qed.
End HomotopyAffinePowerFields.
