(** Federer (1969), 4.1.7, p. 359:
    the literal weight ||Lambda_m Df(vec T)||
    defines a Radon measure on U.
    The original countable compact neighbourhoods,
    finite compact integrals and measurable density
    laws of Chapter 2 supply regularity.
    No finite total mass is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground RealMetricBackground FiniteCoordinates Hom RealNormUP NormMetric NormMetricContinuity NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain
  CurrentCoefficientNorms CurrentMultivectorDual CurrentImageDensityPairing CurrentImageDensityMeasurable
  SmoothDomainCompactOpenCover CountableRadonDensity MeasurableCompactNormIntegral
  OpenFamilyTopologyMathcomp PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP RadonBorelRegularity MeasureDensity MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureSubsetIntegral MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic MeasureStepIntegralIdentification SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentImageWeightRadon.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation UT := (current_domain R v U).
Local Notation Z := (exterior_power Y m).
Local Notation ZN := (@current_vector_mass R h2 n m).
Local Notation hZN := (@current_vector_mass_real_norm R h2 n m).
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable xi:UT->exterior_power X m.
Hypothesis hUnit:forall x,@current_vector_mass R h2 v m (xi x)<=1.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space
    (@current_multivector_weak_laws R v m).1))).
Local Notation image := (@current_image_density R v n m U f xi).
Local Notation H := (real_total_integrand (fun x=>ZN (image x))).
Local Notation lambda := (measure_with_density mu H).

(** Source for [current_image_weight_nonnegative]:
    the original exterior-image mass is nonnegative,
    supporting the density measure in Federer
    4.1.7, p. 359. *)
Lemma current_image_weight_nonnegative:
  measure_almost_everywhere mu (partial_extended_nonnegative_locus H).
Proof.
apply:(@measure_almost_everywhere_mono R UT mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _.
exists (ZN (image x))%:E;split;first by rewrite real_total_integrand_graph.
rewrite lee_fin;exact:real_seminorm_nonnegative hZN.1 _.
Qed.

(** Source for [current_image_weight_measurable]:
    the exact original exterior-image mass is
    measurable, supporting Federer 4.1.7, p. 359.
    The norm is applied to the actual
    image, without a coarse Lipschitz substitute. *)
Lemma current_image_weight_measurable:is_measure_measurable_function mu H.
Proof.
have hImageM:=@current_image_density_measurable R h2 v n m U V hU hV f hImage hf
  xi hUnit mu hm hr hXi.
have hNorm:=@measurable_total_borel_postcomposition R UT (real_norm_metric_space hZN)
  (real_line_metric R) mu hm (fun x=>(image x:real_norm_metric_space hZN)) (fun z=>ZN z)
  hImageM (continuous_borel_function (@real_norm_metric_norm_continuous R Z ZN hZN)).
exact:(@measurable_partial_real_embedding R UT mu hm _ hNorm).
Qed.

(** Source for [current_image_weight_compact_integral]:
    every original compact subset of U
    has a finite integral of the exact
    image weight, supporting Federer 4.1.7,
    p. 359. Properness will be needed
    only when pushing this measure forward. *)
Lemma current_image_weight_compact_integral K:compact K->
  exists c:R,is_measure_subset_integral mu K H c%:E.
Proof.
move=>hK.
have hImageM:=@current_image_density_measurable R h2 v n m U V hU hV f hImage hf
  xi hUnit mu hm hr hXi.
have [C [hC hBound]]:=@current_image_density_compact_bound R h2 v n m U V hU hV
  f hImage hf xi hUnit K hK.
exact:(@measurable_compact_norm_integral R UT Z ZN hZN mu hm hr image K C hImageM hK hC hBound).
Qed.

(** Source for [current_image_weight_compact_finite]:
    the literal density measure is finite
    on every original compact subset, supporting
    Federer 4.1.7, p. 359, by 2.4.10,
    p. 85. *)
Lemma current_image_weight_compact_finite K:compact K->(lambda K < +oo)%E.
Proof.
move=>hK;have [c hC]:=current_image_weight_compact_integral hK.
rewrite (measure_with_density_laws mu H K) /measure_subset_upper_integral.
have hValue:=@measure_upper_integral_unique R UT mu _ _ _
  (measure_upper_integral_specification _ _) hC.2.1.
by rewrite hValue ltry.
Qed.

(** Source for [current_image_weight_radon]:
    the original weighted variation measure is
    Radon on U, supporting the sharp
    inequality in Federer 4.1.7, p. 359.
    Arbitrary open source domains and both
    zero-dimensional endpoints are retained. *)
Theorem current_image_weight_radon:is_radon_measure lambda.
Proof.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX v (@coordinate_basis R v)
    (@coordinate_basisP R v) U hU.
exact:(@countable_compact_finite_radon_density R
  (metric_subset (U:set (real_norm_metric_space hNX))) mu lambda hm hr H C W
  (measure_with_density_laws mu H) current_image_weight_measurable current_image_weight_nonnegative
  (fun K hK=>@current_image_weight_compact_finite K hK) hC hW hWC hCover hWCover).
Qed.
End CurrentImageWeightRadon.
