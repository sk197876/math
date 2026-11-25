(** Federer (1969), 4.1.18, p. 375: the
    original upper measure is literally the reflected
    average of the actual image measures tau_z#||T||,
    rather than a merely named majorant. Both the
    all-set image identity and compact-test integral
    are retained.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed NormalisedDistributionRepresentationUP
  DistributionIntegrationRepresentationUP CurrentAmbientVariation EuclideanRadonTranslation
  CurrentSmoothingVariationAverage EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP
  MeasureUP MeasurePushforward RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingVariationTranslatedMeasures.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable T:@current_space R h2 n Full hFull m.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Local Notation beta:=(@NormalisedCurrent.measure R h2 n m Full hFull T hT).
Local Notation hNorm:=(@NormalisedCurrent.laws R h2 n m Full hFull T hT).
Local Notation hRep:=(normalised_distribution_representation_laws hNorm).
Local Notation hm:=(distribution_representation_measure hRep).
Local Notation hr:=(distribution_representation_radon hRep).

(** Source for [current_translated_ambient_variation]:
    the original translated image of ||T|| in
    the displayed upper measure of 4.1.18, p. 375. *)
Definition current_translated_ambient_variation (z:X):set XT->\bar R:=
  @euclidean_radon_translation R n beta z.

(** Source for [current_translated_ambient_variation_actual]:
    the measure used in the original average is
    literally tau_z#||T|| on every set, supporting
    Federer 4.1.18, p. 375. *)
Theorem current_translated_ambient_variation_actual z:
  current_translated_ambient_variation z=
    measure_pushforward (fun x:XT=>x+z) (@current_ambient_variation R h2 n m T hT).
Proof. apply:funext=>A;reflexivity. Qed.

(** Source for [current_translated_ambient_variation_laws]:
    every literal translated original variation is
    Radon, as required by the averaged measure
    assertion of Federer 4.1.18, p. 375. *)
Theorem current_translated_ambient_variation_laws z:
  is_measure (current_translated_ambient_variation z) /\
  is_radon_measure (current_translated_ambient_variation z).
Proof. exact:(@euclidean_radon_translation_laws R n beta hm hr z). Qed.

Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation nu:=(@current_smoothing_variation_average R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation hNu:=(@current_smoothing_variation_average_laws R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon).

(** Source for [current_smoothing_variation_average_translated_measures]:
    the literal weak integral of the actual translated
    Radon variations in Federer 4.1.18, p. 375.
    Every compact positive test gives the displayed
    reflected scalar integral, including infinite total
    variation of the original current. *)
Theorem current_smoothing_variation_average_translated_measures (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z:X=>family epsilon (-z)*
      @radon_positive_compact_integral R XT (current_translated_ambient_variation z)
        (current_translated_ambient_variation_laws z).1
        (current_translated_ambient_variation_laws z).2 f))
    (@radon_positive_compact_integral R XT nu hNu.1 hNu.2.1 f)%:E.
Proof.
move=>hF.
have hFunction:(fun z:X=>family epsilon (-z)*
      @radon_positive_compact_integral R XT (current_translated_ambient_variation z)
        (current_translated_ambient_variation_laws z).1
        (current_translated_ambient_variation_laws z).2 f)=
    (fun z:X=>family epsilon (-z)*
      @radon_positive_compact_integral R FT beta hm hr (fun x:FT=>f (set_val x+z))).
  apply:funext=>z.
  have hActual:=@radon_positive_compact_integral_laws R XT
    (current_translated_ambient_variation z)
    (current_translated_ambient_variation_laws z).1
    (current_translated_ambient_variation_laws z).2 f hF.
  have hLiteral:=@radon_positive_compact_integral_laws R XT
    (@euclidean_radon_translation R n beta z)
    (@euclidean_radon_translation_laws R n beta hm hr z).1
    (@euclidean_radon_translation_laws R n beta hm hr z).2 f hF.
  have hValue:=EFin_inj (measure_integral_unique hActual hLiteral).
  rewrite hValue (@euclidean_radon_translation_compact_value R n beta hm hr z f hF).
  reflexivity.
rewrite hFunction.
exact:(@current_smoothing_variation_average_translation R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon f hF).
Qed.
End CurrentSmoothingVariationTranslatedMeasures.
