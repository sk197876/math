(** Federer (1969), 4.1.7, p. 359:
    the actual support-proper pushforward remains
    representable by integration, and its original
    variation is bounded by the exact weighted
    image measure. The proof uses the original
    scalar-test gauge of 4.1.5, pp. 349–350,
    without assuming a target representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing CurrentDomain
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP RealFunctionalNormUP
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentImageDensityPairing CurrentPushforwardWeight
  CurrentProperSupport CurrentProperSupportDomain CurrentPushforwardSealed CurrentPushforwardIntegralAction
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP
  DistributionVariationBasic DistributionFiniteGaugeBound DistributionFiniteVariationUP
  FunctionLatticeUP CompactSupportFunctionUP RealIntegralFunctionalUP RadonCompactScalarIntegral
  RadonPositiveCompactComparison DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardVariation.
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
Local Notation A := (A_m Y R^o m).
Local Notation AN := (@current_form_comass R h2 n m).
Local Notation hAN := (@current_form_comass_real_norm R h2 n m).
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation ev := (@current_test_value R h2 n V hV m).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNY) V A DV
  (smooth_test_values_hom hE)).
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hm:=distribution_representation_measure (normalised_distribution_representation_laws hRepresentation).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation push := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation image := (@current_image_density R v n m U f xi).
Local Notation action := (@current_value R h2 n V hV m push).
Local Notation nu := (@current_pushforward_weight R h2 v n m U V hU f hImage T hT).
Let hn:=@current_pushforward_weight_measure R h2 v n m U V hU f hImage T hT.
Let hrn:=@current_pushforward_weight_radon R h2 v n m U V hU hV f hImage hf T hT hp.
Local Notation F := (@radon_positive_compact_integral R VT nu hn hrn).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R VT)).

(** Source for [current_pushforward_compact_test_bound]:
    every original admissible target test is
    bounded by the exact weighted compact
    scalar integral, supporting Federer 4.1.7,
    p. 359. This bound precedes the
    target integration representation. *)
Lemma current_pushforward_compact_test_bound g:
  Kplus g->forall phi:DV,(forall y,AN (dvalues phi y)<=g y)->action phi<=F g.
Proof.
move=>hG phi hPhi.
have hOriginal:=@current_pushforward_original_integral_action R h2 v n m U V hU hV
  T hT f hImage hf hp phi.
have hWeight:=@current_pushforward_weight_compact_integral R h2 v n m U V hU hV
  f hImage hf T hT hp g hG.
have hPointwise x:pairing (image x) (ev phi (f (set_val x)))<=
    g (fU x)*@current_vector_mass R h2 n m (image x).
  have hPair:=real_functional_norm_bound
    (continuous_dual_norm_laws (@current_multivector_continuous_dual R h2 n m) (image x))
    (ev phi (f (set_val x))).
  change (is_true (`|@MultivectorDual.evaluation R Y m (image x)
      (ev phi (f (set_val x)))|<=
    @current_vector_mass R h2 n m (image x)*AN (ev phi (f (set_val x))))) in hPair.
  rewrite MultivectorDual.laws in hPair.
  have hScale:=ler_wpM2l (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n m).1
    (image x)) (hPhi (fU x)).
  change (is_true (@current_vector_mass R h2 n m (image x)*AN (ev phi (f (set_val x)))<=
    @current_vector_mass R h2 n m (image x)*g (fU x))) in hScale.
  rewrite mulrC;exact:(le_trans (ler_norm _) (le_trans hPair hScale)).
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand (fun x=>pairing (image x) (ev phi (f (set_val x)))))
      (real_total_integrand (fun x=>g (fU x)*@current_vector_mass R h2 n m (image x)))).
  apply:(@measure_almost_everywhere_mono R UT mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  exists (pairing (image x) (ev phi (f (set_val x))))%:E,
    (g (fU x)*@current_vector_mass R h2 n m (image x))%:E.
  split;first by rewrite real_total_integrand_graph.
  split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;exact:hPointwise x.
have hBound:=@measure_integral_monotone R UT mu hm _ _ _ _ hOriginal hWeight hOrder.
by rewrite lee_fin in hBound.
Qed.

(** Source for [current_pushforward_representable]:
    the original support-proper pushforward of
    an integration-representable current is representable
    by integration, Federer 4.1.7, p. 359.
    Finite scalar-test bounds prove the
    literal original criterion of 4.1.5. *)
Theorem current_pushforward_representable:
  @is_integration_representable_current R h2 n m V hV push.
Proof.
apply:(@current_integration_finite_gauge_criterion R h2 n m V hV push).1=>g hG.
have [b [hB _]]:=@distribution_finite_gauge_from_test_bound R VT A AN hAN DV dvalues
  action g (F g) hG.2 (current_pushforward_compact_test_bound hG).
by exists b.
Qed.

(** Source for [current_pushforward_weighted_variation_bound]:
    ||f#T|| is at most the image
    of ||T|| weighted by the actual
    exterior-image mass, Federer 4.1.7, p. 359.
    The inequality holds on every set,
    including infinite outer masses. *)
Theorem current_pushforward_weighted_variation_bound
    (hPush:@is_integration_representable_current R h2 n m V hV push):
  forall B,(@NormalisedCurrent.measure R h2 n m V hV push hPush B<=nu B)%E.
Proof.
pose rho:=@NormalisedCurrent.measure R h2 n m V hV push hPush.
have hR:=@NormalisedCurrent.laws R h2 n m V hV push hPush.
have hBase:=normalised_distribution_representation_laws hR.
have hRho:=distribution_representation_measure hBase.
have hRadon:=distribution_representation_radon hBase.
pose G:=@radon_positive_compact_integral R VT rho hRho hRadon.
have hG:=@radon_positive_compact_integral_laws R VT rho hRho hRadon.
have hF:=@radon_positive_compact_integral_laws R VT nu hn hrn.
apply:(@radon_positive_compact_integral_comparison R VT rho nu hRho hn hRadon hrn G F hG hF)=>g hg.
have [b [hGauge hIntegral]]:=normalised_distribution_original_gauge hR hg.
have hEqual:=measure_integral_unique hIntegral (hG g hg).
have hBound:=@distribution_variation_least_finite_bound R VT A AN DV dvalues action g b%:E (F g)
  hGauge (current_pushforward_compact_test_bound hg).
rewrite hEqual lee_fin in hBound;exact:hBound.
Qed.
End CurrentPushforwardVariation.
