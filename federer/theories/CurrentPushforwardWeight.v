(** Federer (1969), 4.1.7, p. 359:
    the original weighted image measure in
    the sharp variation inequality is Radon.
    Only f restricted to spt T is
    proper. Concentration of ||T|| on that
    support and the original density-null law
    permit the support-proper Radon image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentImageDensityPairing CurrentImageWeightRadon CurrentProperSupport CurrentProperSupportDomain
  CurrentDomainGeometry CurrentRadonSupport RadonCarriedProperPushforward MeasureUP MeasurePushforward
  MeasureDensity MeasureDensityNullSets RadonMeasureUP PartialFunctionBasic PartialExtendedOrderLoci
  SummableRealFunctionUP DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  SubtypeCompactHausdorff FunctionLatticeUP CompactSupportFunctionUP MeasureIntegralUP
  RadonCompactScalarIntegral RadonWeightedPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardWeight.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Let hUnit:=normalised_distribution_density_unit_bound hRepresentation.
Let hXi:=distribution_representation_weak_measurable hBase.
Local Notation H := (real_total_integrand (fun x=>@current_vector_mass R h2 n m
  (@current_image_density R v n m U f xi x))).
Local Notation lambda := (measure_with_density mu H).

(** Source for [current_pushforward_weight]: the
    image of ||T|| restricted by the
    actual exterior-image mass, supporting the
    exact printed inequality in Federer 4.1.7,
    p. 359. The auxiliary density will
    be identified with the original maximal
    orienting field almost everywhere. *)
Definition current_pushforward_weight:set VT->\bar R:=measure_pushforward fU lambda.

(** Source for [current_pushforward_weight_measure]:
    the original nonnegative weighted image is
    a measure, supporting Federer 4.1.7,
    p. 359. Its total mass may
    be infinite. *)
Lemma current_pushforward_weight_measure:is_measure current_pushforward_weight.
Proof.
apply:measure_pushforward_is_measure.
exact:(@measure_with_density_is_measure R UT mu hm H
  (@current_image_weight_nonnegative R h2 v n m U f mu hm xi)).
Qed.

(** Source for [current_pushforward_weight_radon]:
    original support-properness gives a Radon
    weighted image measure on V, supporting
    Federer 4.1.7, p. 359. No
    separate properness or compact support
    assumption on the whole U is added. *)
Theorem current_pushforward_weight_radon:
  @is_current_proper_on_support R h2 v n m U hU V T f hImage->
  is_radon_measure current_pushforward_weight.
Proof.
move=>hp.
have hLambda:is_measure lambda.
  exact:(@measure_with_density_is_measure R UT mu hm H
    (@current_image_weight_nonnegative R h2 v n m U f mu hm xi)).
have hLambdaRadon:=@current_image_weight_radon R h2 v n m U V hU hV f hImage hf
  mu hm hr xi hUnit hXi.
pose S:set UT:=[set x|@current_support R h2 v U hU m T (set_val x)].
have hCarried:lambda (~` S)=0.
  exact:(@measure_density_null_set R UT mu lambda hm H (~` S)
    (measure_with_density_laws mu H) (@current_radon_outside_support_null R h2 v m U hU T hT)).
have hContinuous:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
have hProper:=@current_domain_proper_on_support R h2 v n U V f hImage m hU T hp.
have hHausdorff:hausdorff_space VT.
  exact:(@set_type_hausdorff (real_norm_metric_space hNY) V
    (@metric_hausdorff R (real_norm_metric_space hNY))).
exact:(@carried_proper_radon_pushforward R UT VT lambda hLambda hLambdaRadon S hCarried
  fU hContinuous hHausdorff (@current_domain_locally_compact R n V hV) hProper).
Qed.
(** Source for [current_pushforward_weight_compact_integral]:
    each original positive compact scalar test
    has the exact source weighted integral,
    supporting the sharp gauge bound in
    Federer 4.1.7, p. 359, by
    2.4.10 and 2.4.18. *)
Theorem current_pushforward_weight_compact_integral
    (hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage) g:
  positive_function_lattice (@compactly_supported_continuous_functions R VT) g->
  is_measure_integral mu (real_total_integrand (fun x=>g (fU x)*
    @current_vector_mass R h2 n m (@current_image_density R v n m U f xi x)))
    (@radon_positive_compact_integral R VT current_pushforward_weight
      current_pushforward_weight_measure (current_pushforward_weight_radon hp) g)%:E.
Proof.
move=>hG.
have hPositive:=@current_image_weight_nonnegative R h2 v n m U f mu hm xi.
have hLambda:=@measure_with_density_is_measure R UT mu hm H hPositive.
have hLambdaRadon:=@current_image_weight_radon R h2 v n m U V hU hV f hImage hf
  mu hm hr xi hUnit hXi.
have hMeas:=@current_image_weight_measurable R h2 v n m U V hU hV f hImage hf
  mu hm hr xi hUnit hXi.
have hContinuous:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
exact:(@radon_weighted_pushforward_compact_integral R UT VT mu lambda hm hr hLambda hLambdaRadon
  (fun x=>@current_vector_mass R h2 n m (@current_image_density R v n m U f xi x)) fU
  (measure_with_density_laws mu H) hMeas hPositive hContinuous
  current_pushforward_weight_measure (current_pushforward_weight_radon hp) g hG).
Qed.
End CurrentPushforwardWeight.
