(** Federer (1969), 4.1.7, p. 359:
    the actual proper pushforward of an
    integration-representable current has the original
    exterior-image pairing integral. The compact
    replacement formula and concentration on spt T
    justify the equality before any target
    representation or variation bound is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing CurrentDomain
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentImageDensityPairing CurrentRadonSupport
  CurrentProperSupport CurrentPushforwardUP CurrentPushforwardExistence CurrentPushforwardSealed
  SmoothFormPullbackSealed SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP MultivectorDualSealed
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardIntegralAction.
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
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation evU := (@current_test_value R h2 v U hU m).
Local Notation evV := (@current_test_value R h2 n V hV m).
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation push := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Local Notation image := (@current_image_density R v n m U f xi).

(** Source for [current_pushforward_original_integral_action]:
    every original target test is evaluated
    by pairing with Lambda_m Df(x)(vec T(x))
    under ||T||, Federer 4.1.7, p. 359.
    The normalized auxiliary density equals the
    original orienting field almost everywhere;
    no target density is assumed here. *)
Theorem current_pushforward_original_integral_action (phi:DV):
  is_measure_integral mu
    (real_total_integrand (fun x=>pairing (image x) (evV phi (f (set_val x)))))
    (@current_value R h2 n V hV m push phi)%:E.
Proof.
have [psi hReplacement]:=@current_pushforward_test_replacement_exists R h2 v n m U V hU hV
  T f hImage hf hp phi.
have hValue:=@CurrentPushforward.laws R h2 v n m U V hU hV T f hImage hf hp
  phi psi hReplacement.
have [W [hW [hTW [hWU hAgreement]]]]:=hReplacement.
have hSource:=distribution_representation_action hBase psi.
have hEvals:(fun x:UT=>@MultivectorDual.evaluation R X m (xi x) (evU psi (set_val x)))=
    (fun x=>pairing (xi x) (evU psi (set_val x))).
  apply:funext=>x;exact:MultivectorDual.laws.
change (is_measure_integral mu (real_total_integrand
  (fun x=>@MultivectorDual.evaluation R X m (xi x) (evU psi (set_val x))))
  (@current_value R h2 v U hU m T psi)%:E) in hSource.
rewrite hEvals -hValue in hSource.
apply:(@measure_integral_almost_equal R UT mu hm _ _ _ hSource).
have hSupport:measure_almost_everywhere mu [set x:UT|@current_support R h2 v U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 v m U hU T hT).
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupport)=>x hx.
have hPair:=@current_image_density_pairing R h2 v n m U V hU hV f hImage hf
  xi (smooth_test_inclusion hE phi) x.
change (pairing (image x) (evV phi (f (set_val x)))=
  pairing (xi x) (fv (pull (smooth_test_inclusion hE phi)) (set_val x))) in hPair.
rewrite -(hAgreement (set_val x) (hTW (set_val x) hx)) in hPair.
exists (pairing (xi x) (evU psi (set_val x)))%:E;split;
  rewrite real_total_integrand_graph;first by [].
by rewrite hPair.
Qed.
End CurrentPushforwardIntegralAction.
