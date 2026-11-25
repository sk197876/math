(** Federer (1969), 4.1.17, p. 374: the original compact
    smooth i-form tests are dense for the L1 seminorm of ||T||.
    Reuse the proved test density of 4.1.5, p. 350, with the
    actual finite covector space, its original comass norm and
    the actual Radon variation of T. Every original conull
    partial domain is retained in the final density statement. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentIntegrationCriterion NormalisedCurrentSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationDomain SmoothTestLoneDensity CurrentMeasurableMultiplierUP
  VectorDaniellHypotheses VectorDaniellRationalSpan
  RadonCompactScalarIntegral RadonBorelRegularity
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP SummableSubsetRestriction PartialFunctionUP PartialFunctionBasic
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasureLpNorm MeasureLpMembershipUP
  MeasureLpConvergence SeparableVectorLone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentVariationFormLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m k:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o k).
Local Notation NY := (@current_form_comass R h2 n k).
Local Notation hNY := (@current_form_comass_real_norm R h2 n k).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hRepresentation := (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Local Notation hm := (distribution_representation_measure hRepresentation).
Local Notation hr := (distribution_representation_radon hRepresentation).
Local Notation E := (@current_smooth_space R h2 n U hU k).
Local Notation ev := (@current_smooth_value R h2 n U hU k).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU k).
Local Notation DT := (@current_test_space R h2 n U hU k).
Local Notation test := (fun psi:DT=>fun x:UT=>
  @current_test_value R h2 n U hU k psi (set_val x)).

(** Source for [current_variation_form_lone_norm_integral]:
    a summable original coefficient has a finite norm integral,
    as used in the L1 approximation proof of Federer 4.1.17,
    p. 374, by the original 2.4.12 convention, p. 86. *)
Lemma current_variation_form_lone_norm_integral (f:UT->Y):
  is_measure_lp_function mu 1 (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  exists a:R,is_measure_integral mu
    (real_total_integrand (fun x=>NY (f x))) a%:E.
Proof.
move=>hF.
have hPositive:=@measure_lp_norm_nonnegative R UT Y NY hNY mu 1
  (partial_function_total (fun x=>(f x:real_norm_metric_space hNY)))
  hm (lexx _) hF.2.1.1.
have hFinite:measure_lp_norm mu NY 1
    (partial_function_total (fun x=>(f x:real_norm_metric_space hNY)))
    \is a fin_num.
  rewrite (ge0_fin_numE hPositive);exact:hF.2.2.1.
exists (fine (measure_lp_norm mu NY 1
  (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))))).
rewrite fineK //.
exact:(@total_vector_norm_integral R UT Y NY hNY mu hm
  (fun x=>(f x:real_norm_metric_space hNY)) hF.2.1.1).
Qed.

(** Source for [current_variation_form_lone_locally_summable]:
    every original variation-summable coefficient satisfies the
    local hypothesis of the already defined measurable contraction,
    supporting Federer 4.1.17, p. 374, through 4.1.7,
    pp. 355–356. No finite total variation is needed here. *)
Theorem current_variation_form_lone_locally_summable (f:UT->Y):
  is_measure_lp_function mu 1 (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  is_locally_summable_current_field hNY mu f.
Proof.
move=>hF;split;first exact:hF.2.1.1.
have hSummable:=current_variation_form_lone_norm_integral hF.
move=>K hK.
exact:(@summable_measurable_zero_extension R UT mu hm K
  (real_total_integrand (fun x=>NY (f x)))
  (@radon_compact_measurable R UT mu hm hr K hK) hSummable).
Qed.

(** Source for [current_variation_summable_form_lone]: the
    original measurable and norm-summable coefficient convention
    suffices for L1 membership in Federer 4.1.17, p. 374.
    Countable measurability is proved from the finite-dimensional
    covector space; it is not an additional hypothesis. *)
Theorem current_variation_summable_form_lone (f:UT->Y):
  is_measure_measurable_function mu (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  is_measure_summable mu (real_total_integrand (fun x=>NY (f x)))->
  is_measure_lp_function mu 1 (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY))).
Proof.
move=>hF [a hIntegral].
have[D hD]:=rational_dense_subspace_exists (@current_form_separable R h2 n k).
exact:(@separable_vector_summable_norm_lone R UT Y NY hNY D hD mu hm
  (fun x=>(f x:real_norm_metric_space hNY)) a hF hIntegral).
Qed.

(** Source for [current_variation_form_test_lone_dense]: compact
    smooth i-form tests approximate every total original L1
    coefficient with arbitrarily small finite norm integral,
    exactly the density used in Federer 4.1.17, p. 374.
    Both the coefficient degree and the ambient dimension may
    be zero, and the open domain may be empty. *)
Theorem current_variation_form_test_lone_dense (f:UT->Y):
  is_measure_lp_function mu 1 (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  forall epsilon:R,0<epsilon->exists psi:DT,exists a:R,
    is_measure_integral mu (real_total_integrand
      (fun x=>NY (f x-test psi x))) a%:E /\a<epsilon.
Proof.
exact:(@smooth_test_lone_total_dense R n Y NY hNY
  (@current_form_complete R h2 n k) (@current_form_separable R h2 n k)
  U hU E ev hE mu hm hr
  (@radon_positive_compact_integral R UT mu hm hr)
  (@radon_positive_compact_integral_laws R UT mu hm hr)
  (fun x=>(f x:real_norm_metric_space hNY))).
Qed.

(** Source for [current_variation_form_test_partial_lone_dense]:
    the original L1 density assertion also retains every original
    conull partial coefficient, Federer 4.1.17, p. 374, by
    4.1.5, p. 350. Each approximating test is itself L1 and
    the distance is measured on the original partial domain. *)
Theorem current_variation_form_test_partial_lone_dense
    (f:partial_function UT (real_norm_metric_space hNY)):
  is_measure_lp_function mu 1 f->
  forall epsilon:R,0<epsilon->exists psi:DT,
    is_measure_lp_function mu 1 (partial_function_total
      (fun x=>(test psi x:real_norm_metric_space hNY))) /\
    (measure_lp_distance mu NY 1 f (partial_function_total
      (fun x=>(test psi x:real_norm_metric_space hNY)))<epsilon%:E)%E.
Proof.
exact:(@smooth_test_lone_dense R n Y NY hNY
  (@current_form_complete R h2 n k) (@current_form_separable R h2 n k)
  U hU E ev hE mu hm hr
  (@radon_positive_compact_integral R UT mu hm hr)
  (@radon_positive_compact_integral_laws R UT mu hm hr) f).
Qed.
End CurrentVariationFormLone.
