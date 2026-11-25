(** Federer (1969), 4.1.14, p. 371: the right side
    f#(||T|| sigma^m) is the literal weighted image measure
    on the original open source. This supporting interface
    permits every continuous nonnegative original weight.
    It uses properness only on the actual current support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentProperSupport CurrentProperSupportDomain
  CurrentDomainGeometry CurrentRadonSupport SmoothDomainCompactOpenCover
  ContinuousRadonDensity RadonCarriedProperPushforward MeasureUP MeasureDensity
  MeasureDensityNullSets MeasurePushforward MeasureAlmostUP
  RadonMeasureUP PartialFunctionBasic SummableRealFunctionUP
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  SubtypeCompactHausdorff MetricSubsetBackground FunctionLatticeUP CompactSupportFunctionUP
  MeasureIntegralUP RadonCompactScalarIntegral RadonWeightedPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentContinuousPushforwardWeight.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Local Notation UT:=(current_domain R n U).
Local Notation UM:=(metric_subset (U:set (real_norm_metric_space hNX))).
Local Notation VT:=(current_domain R nu V).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Let hRepresentation:=@NormalisedCurrent.laws R h2 n m U hU T hT.
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Variable w:UT->R^o.
Hypothesis hW:continuous w.
Hypothesis hPositive:forall x,0<=w x.
Local Notation H:=(real_total_integrand w).
Local Notation lambda:=(measure_with_density mu H).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_zero NX NY U f.
Local Notation fU:=(@current_map_on_domain R n nu U V f hImage).

(** Source for [current_continuous_pushforward_weight]: the
    literal image of the original variation weighted by w,
    supporting Federer 4.1.14, p. 371. No derivative or
    smoothed current is used to define this measure. *)
Definition current_continuous_pushforward_weight:set VT->\bar R:=
  measure_pushforward fU lambda.

(** Source for [current_continuous_source_weight_measure]:
    the original continuous nonnegative weight defines a measure,
    supporting Federer 4.1.14, p. 371, by 2.4.10, p. 85. *)
Lemma current_continuous_source_weight_measure:is_measure lambda.
Proof.
apply:(@measure_with_density_is_measure R UT mu hm H).
exact:(@continuous_radon_density_nonnegative R UM mu hm w hPositive).
Qed.

(** Source for [current_continuous_source_weight_radon]: the
    original weighted variation is Radon on arbitrary open U,
    supporting Federer 4.1.14, p. 371. *)
Lemma current_continuous_source_weight_radon:is_radon_measure lambda.
Proof.
have[C [W [hC [hOpen [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
exact:(@continuous_radon_density_radon R UM mu hm hr w hW hPositive C W
  hC hOpen hWC hCover hWCover).
Qed.

(** Source for [current_continuous_pushforward_weight_measure]:
    the original weighted image is a measure, supporting
    Federer 4.1.14, p. 371. Infinite outer masses remain allowed. *)
Lemma current_continuous_pushforward_weight_measure:
  is_measure current_continuous_pushforward_weight.
Proof.
exact:measure_pushforward_is_measure current_continuous_source_weight_measure.
Qed.

(** Source for [current_continuous_pushforward_weight_radon]:
    properness only on sptT makes the literal weighted
    image Radon, supporting Federer 4.1.14, p. 371. *)
Theorem current_continuous_pushforward_weight_radon:
  @is_current_proper_on_support R h2 n nu m U hU V T f hImage->
  is_radon_measure current_continuous_pushforward_weight.
Proof.
move=>hp.
pose S:set UT:=[set x|@current_support R h2 n U hU m T (set_val x)].
have hCarried:lambda (~` S)=0.
  exact:(@measure_density_null_set R UT mu lambda hm H (~` S)
    (measure_with_density_laws mu H)
    (@current_radon_outside_support_null R h2 n m U hU T hT)).
have hContinuous:=@current_map_on_domain_continuous R n nu U V f hImage hf.
have hProper:=@current_domain_proper_on_support R h2 n nu U V f hImage m hU T hp.
have hHausdorff:hausdorff_space VT.
  exact:(@set_type_hausdorff (real_norm_metric_space hNY) V
    (@metric_hausdorff R (real_norm_metric_space hNY))).
exact:(@carried_proper_radon_pushforward R UT VT lambda
  current_continuous_source_weight_measure current_continuous_source_weight_radon
  S hCarried fU hContinuous hHausdorff
  (@current_domain_locally_compact R nu V hV) hProper).
Qed.

(** Source for [current_continuous_pushforward_weight_compact_integral]:
    positive compact scalar tests have exactly the printed
    weighted source integral, supporting Federer 4.1.14,
    p. 371, by 2.4.10 and 2.4.18, pp. 85 and 90. *)
Theorem current_continuous_pushforward_weight_compact_integral
    (hp:@is_current_proper_on_support R h2 n nu m U hU V T f hImage) h:
  positive_function_lattice (@compactly_supported_continuous_functions R VT) h->
  is_measure_integral mu (real_total_integrand (fun x=>h (fU x)*w x))
    (@radon_positive_compact_integral R VT current_continuous_pushforward_weight
      current_continuous_pushforward_weight_measure
      (current_continuous_pushforward_weight_radon hp) h)%:E.
Proof.
move=>hH.
exact:(@radon_weighted_pushforward_compact_integral R UT VT mu lambda hm hr
  current_continuous_source_weight_measure current_continuous_source_weight_radon
  w fU (measure_with_density_laws mu H)
  (@continuous_radon_density_measurable R UM mu hm hr w hW)
  (@continuous_radon_density_nonnegative R UM mu hm w hPositive)
  (@current_map_on_domain_continuous R n nu U V f hImage hf)
  current_continuous_pushforward_weight_measure
  (current_continuous_pushforward_weight_radon hp) h hH).
Qed.
End CurrentContinuousPushforwardWeight.
