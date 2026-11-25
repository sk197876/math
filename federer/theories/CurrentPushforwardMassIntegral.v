(** Federer (1969), 4.1.11, p. 365: apply the exact
    mass bound for a proper pushforward, using the original
    exterior differential weight of 4.1.7, p. 359. The
    total mass and the nonnegative integral may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric
  NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentImageDensityPairing
  CurrentImageWeightRadon CurrentProperSupport CurrentProperSupportDomain CurrentPushforwardSealed
  CurrentPushforwardWeight CurrentPushforwardVariation CurrentMassSealed CurrentMassRepresentation
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP MeasurePushforward MeasureDensity
  PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws SummableRealFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardMassIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y.
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation UT := (current_domain R v U).
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 v m U hU T hT).
Local Notation hNormal := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Local Notation hm := (distribution_representation_measure (normalised_distribution_representation_laws hNormal)).
Local Notation hr := (distribution_representation_radon (normalised_distribution_representation_laws hNormal)).
Local Notation W := (real_total_integrand (fun x=>@current_vector_mass R h2 n m
  (@current_image_density R v n m U f xi x))).
Local Notation image := (@current_map_on_domain R v n U V f hImage).
Local Notation nu := (@current_pushforward_weight R h2 v n m U V hU f hImage T hT).
Local Notation push := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Local Notation I := (measure_lower_integral mu W).

(** Source for [current_pushforward_mass_weight_integral]:
    the actual exterior-image weight has its nonnegative
    integral, supporting the sharp join estimate in
    Federer 4.1.11, p. 365, by 2.4.4(2), p. 82. *)
Theorem current_pushforward_mass_weight_integral:is_measure_integral mu W I.
Proof.
exact:(@nonnegative_measurable_function_integral R UT mu hm W
  (@current_image_weight_measurable R h2 v n m U V hU hV f hImage hf mu hm hr xi
    (normalised_distribution_density_unit_bound hNormal)
    (distribution_representation_weak_measurable (normalised_distribution_representation_laws hNormal)))
  (@current_image_weight_nonnegative R h2 v n m U f mu hm xi)).1.
Qed.

(** Source for [current_pushforward_mass_weight_total]:
    the total weighted image equals the original exact
    weight integral, supporting Federer 4.1.11, p. 365,
    by the density definition of 2.4.10, p. 85. *)
Theorem current_pushforward_mass_weight_total:nu setT=I.
Proof.
have hWhole:is_measure_integral mu
    (partial_function_zero_extension (0:extended_real_line R) setT W) I.
  apply:(@measure_integral_graph_equivalent R UT mu _ _ _ _ current_pushforward_mass_weight_integral)=>x z.
  exact:iff_sym (partial_zero_extension_whole_graph (0:extended_real_line R) W x z).
have hUpper:=@measure_upper_integral_unique R UT mu _ _ I
  (measure_upper_integral_specification mu _) hWhole.2.1.
change (measure_with_density mu W (image @^-1` setT)=I).
have hSet:image @^-1` setT=setT by apply/seteqP;split=>x;by [].
rewrite hSet (measure_with_density_laws mu W setT).
exact:hUpper.
Qed.

(** Source for [current_pushforward_mass_integral_bound]:
    M(f#T) is at most the integral of the exact mass
    of Lambda_m Df applied to the original normalized
    density, supporting Federer 4.1.11, p. 365, through
    4.1.7, pp. 358–359. Only support properness is needed. *)
Theorem current_pushforward_mass_integral_bound:
  (@CurrentMass.value R h2 n m V hV push<=I)%E.
Proof.
pose hPush:=@current_pushforward_representable R h2 v n m U V hU hV T hT f hImage hf hp.
rewrite (@current_represented_mass_total R h2 n m V hV push hPush).
apply:(le_trans (@current_pushforward_weighted_variation_bound R h2 v n m U V hU hV
  T hT f hImage hf hp hPush setT)).
rewrite current_pushforward_mass_weight_total;exact:lexx.
Qed.
End CurrentPushforwardMassIntegral.
