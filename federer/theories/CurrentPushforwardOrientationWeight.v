(** Federer (1969), 4.1.7, p. 359:
    the sharp measure inequality uses Federer's
    original maximal partial orienting field vec T.
    The normalized auxiliary representative gives
    exactly the same density measure because
    the original fields agree almost everywhere.
    No value is assigned outside the original
    orienting field's partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorMaps CurrentDomain CurrentCoefficientNorms
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMapDifferential CurrentImageDensityPairing
  CurrentOrientationSealed CurrentOrientationAlmost CurrentProperSupport CurrentProperSupportDomain
  CurrentPushforwardSealed CurrentPushforwardWeight CurrentPushforwardVariation
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensity MeasureDensityTransfer MeasurePushforward
  RadonMeasureUP SummableRealFunctionUP DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardOrientationWeight.
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
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hm:=distribution_representation_measure (normalised_distribution_representation_laws hRepresentation).
Local Notation P := (@CurrentOrientation.value R h2 v m U hU T hT).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation push := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation H := (real_total_integrand (fun x=>@current_vector_mass R h2 n m
  (@current_image_density R v n m U f xi x))).
Local Notation lambda := (measure_with_density mu H).

(** Source for [current_original_image_weight]: the
    literal partial function ||Lambda_m Df(vec T)||,
    supporting the original variation bound in
    Federer 4.1.7, p. 359. This is
    only pairing and composition of the
    already specified original partial functions. *)
Definition current_original_image_weight:partial_function UT (extended_real_line R):=
  partial_function_postcompose (partial_function_pair (partial_function_total (fun x:UT=>x)) P)
    (fun p:UT*exterior_power X m=>(@current_vector_mass R h2 n m
      (exterior_power_map (hom_as_linear (@current_map_differential R v n U f (set_val p.1))) m p.2))%:E).

(** Source for [current_original_image_weight_agreement]:
    the printed partial weight equals the
    auxiliary total weight almost everywhere under
    ||T||, supporting Federer 4.1.7, p. 359.
    The exact original partial domain is retained. *)
Lemma current_original_image_weight_agreement:measure_almost_equal mu current_original_image_weight H.
Proof.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _
  (@current_orientation_normalised_agreement R h2 v m U hU T hT))=>x hP.
exists (@current_vector_mass R h2 n m (@current_image_density R v n m U f xi x))%:E;split.
- exists (x,xi x);split.
  + split;first by [].
    exact:hP.
  + by [].
- by rewrite real_total_integrand_graph.
Qed.

(** Source for [current_original_image_density_measure]:
    the actual density measure from Federer's
    original partial vec T is exactly the
    auxiliary density measure, supporting the
    printed formula in 4.1.7, p. 359,
    by 2.4.10, p. 85. *)
Lemma current_original_image_density_measure:
  measure_with_density mu current_original_image_weight=lambda.
Proof.
have hLaws:=@measure_density_almost_equal R UT mu
  (measure_with_density mu current_original_image_weight) hm current_original_image_weight H
  (measure_with_density_laws mu current_original_image_weight) current_original_image_weight_agreement.
apply:funext=>A;exact:(eq_trans (hLaws A) (esym (measure_with_density_laws mu H A))).
Qed.

(** Source for [current_original_pushforward_weight_radon]:
    the exact printed weighted image measure
    formed with the original maximal partial
    orientation is Radon, supporting Federer
    4.1.7, p. 359. *)
Theorem current_original_pushforward_weight_radon:
  is_radon_measure (measure_pushforward fU (measure_with_density mu current_original_image_weight)).
Proof.
rewrite current_original_image_density_measure.
exact:(@current_pushforward_weight_radon R h2 v n m U V hU hV f hImage hf T hT hp).
Qed.

(** Source for [current_pushforward_original_weighted_variation]:
    ||f#T|| <= f#(||T|| restricted by
    ||Lambda_m Df(vec T)||), Federer 4.1.7,
    p. 359. This is the original
    partial-orientation formula, on every target set. *)
Theorem current_pushforward_original_weighted_variation
    (hPush:@is_integration_representable_current R h2 n m V hV push):forall B,
  (@NormalisedCurrent.measure R h2 n m V hV push hPush B<=
    measure_pushforward fU (measure_with_density mu current_original_image_weight) B)%E.
Proof.
rewrite current_original_image_density_measure.
exact:(@current_pushforward_weighted_variation_bound R h2 v n m U V hU hV T hT f hImage hf hp hPush).
Qed.
End CurrentPushforwardOrientationWeight.
