(** Federer (1969), 4.1.14, p. 371: before taking
    the smooth approximation limit, bound each target test
    by the original source integral with weight sigma^m.
    The derivative cap is required only on sptT.
    There is no normality or source-variation-AE derivative premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed ContinuousDualUP RealFunctionalNormUP
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentImageDensityPairing
  CurrentImageMajorantBound CurrentRadonSupport CurrentMapDifferential
  EuclideanHomOperator CurrentProperSupport CurrentProperSupportDomain
  CurrentPushforwardSealed CurrentPushforwardIntegralAction
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationDomain DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP PartialFunctionBasic SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSmoothMajorantTestBound.
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
Local Notation VT:=(current_domain R nu V).
Local Notation AN:=(@current_form_comass R h2 nu m).
Local Notation DV:=(@current_test_space R h2 nu V hV m).
Local Notation ev:=(@current_test_value R h2 nu V hV m).
Local Notation hE:=(@current_smooth_space_laws R h2 nu V hV m).
Local Notation dvalues:=(@distribution_domain_values R
  (real_norm_metric_space hNY) V (A_m Y R^o m) DV (smooth_test_values_hom hE)).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi:=(@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Let hNormal:=@NormalisedCurrent.laws R h2 n m U hU T hT.
Let hm:=distribution_representation_measure
  (normalised_distribution_representation_laws hNormal).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hSmooth:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Local Notation fU:=(@current_map_on_domain R n nu U V f hImage).
Local Notation Push:=(@CurrentPushforward.value R h2 n nu m U V hU hV
  T f hImage hSmooth hProper).
Local Notation image:=(@current_image_density R n nu m U f xi).
Variable sigma:X->R.
Hypothesis hCap:forall x,@current_support R h2 n U hU m T x->
  @euclidean_operator_norm R n nu (@current_map_differential R n nu U f x)<=sigma x.
Arguments hCap : clear implicits.

(** Source for [current_smooth_majorant_compact_test_bound]:
    the smoothed weighted scalar estimate in Federer 4.1.14,
    p. 371. The integral is with respect to the actual
    original variation; arbitrary real integral witnesses agree.
    Degree zero, zero caps and empty domains remain included. *)
Theorem current_smooth_majorant_compact_test_bound
    (h:VT->R) (b:R):
  (forall y,0<=h y)->
  is_measure_integral mu
    (real_total_integrand (fun x=>h (fU x)*(sigma (set_val x))^+m)) b%:E->
  forall phi:DV,(forall y,AN (dvalues phi y)<=h y)->
  @current_value R h2 nu V hV m Push phi<=b.
Proof.
move=>hPositive hIntegral phi hPhi.
have hOriginal:=@current_pushforward_original_integral_action R h2 n nu m
  U V hU hV T hT f hImage hSmooth hProper phi.
have hSupport:measure_almost_everywhere mu
    [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hPointwise x:
    @current_support R h2 n U hU m T (set_val x)->
    pairing (image x) (ev phi (f (set_val x)))<=
      h (fU x)*(sigma (set_val x))^+m.
  move=>hx.
  have hPair:=real_functional_norm_bound
    (continuous_dual_norm_laws (@current_multivector_continuous_dual R h2 nu m)
      (image x)) (ev phi (f (set_val x))).
  change (is_true (`|@MultivectorDual.evaluation R Y m (image x)
      (ev phi (f (set_val x)))|<=
    @current_vector_mass R h2 nu m (image x)*AN (ev phi (f (set_val x))))) in hPair.
  rewrite MultivectorDual.laws in hPair.
  have hScale:=ler_wpM2l
    (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 nu m).1 (image x))
    (hPhi (fU x)).
  have hWeight:=@current_image_density_pointwise_majorant R h2 n nu m
    U hU T hT f x (sigma (set_val x)) (hCap (set_val x) hx).
  have hLast:=ler_wpM2l (hPositive (fU x)) hWeight.
  apply:le_trans (ler_norm _) _.
  apply:le_trans hPair _.
  apply:le_trans hScale _.
  by rewrite mulrC;exact:hLast.
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus
      (real_total_integrand (fun x=>pairing (image x) (ev phi (f (set_val x)))))
      (real_total_integrand (fun x=>h (fU x)*(sigma (set_val x))^+m))).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupport)=>x hx.
  exists (pairing (image x) (ev phi (f (set_val x))))%:E,
    (h (fU x)*(sigma (set_val x))^+m)%:E.
  split;first by rewrite real_total_integrand_graph.
  split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;exact:hPointwise x hx.
have hBound:=@measure_integral_monotone R UT mu hm _ _ _ _
  hOriginal hIntegral hOrder.
by rewrite lee_fin in hBound.
Qed.
End CurrentSmoothMajorantTestBound.
