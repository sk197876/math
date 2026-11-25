(** Federer (1969), 4.1.18, p. 375: the
    original variation has the same positive compact
    integrals on the full current domain and its
    ambient Euclidean copy. This is the preceding
    image-integral law, without any change of measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  NormalisedDistributionRepresentationUP DistributionIntegrationRepresentationUP
  CurrentAmbientVariation EuclideanFullDomainCompactFunctions MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness RadonWeightedPushforwardIntegral RadonCompactScalarIntegral
  FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAmbientVariationIntegral.
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
Local Notation hN:=(@NormalisedCurrent.laws R h2 n m Full hFull T hT).
Local Notation hRep:=(normalised_distribution_representation_laws hN).
Local Notation hm:=(distribution_representation_measure hRep).
Local Notation hr:=(distribution_representation_radon hRep).
Local Notation ambient:=(@current_ambient_variation R h2 n m T hT).
Local Notation hAmbient:=(@current_ambient_variation_laws R h2 n m T hT).

(** Source for [current_ambient_variation_positive_compact_value]:
    the exact original positive compact integral is
    preserved by the inverse full-domain copies,
    supporting the translated variation average in
    Federer 4.1.18, p. 375, by 2.4.18, p. 90. *)
Theorem current_ambient_variation_positive_compact_value (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  @radon_positive_compact_integral R XT ambient hAmbient.1 hAmbient.2 f=
    @radon_positive_compact_integral R FT beta hm hr (fun x:FT=>f (set_val x)).
Proof.
move=>hF.
have hFullF:positive_function_lattice (@compactly_supported_continuous_functions R FT)
    (fun x:FT=>f (set_val x)).
  split;first exact:euclidean_full_compact_function_pullback hF.1.
  by move=>x;exact:hF.2 (set_val x).
have hSource:=@radon_positive_compact_integral_laws R FT beta hm hr
  (fun x:FT=>f (set_val x)) hFullF.
have hImage:=(@real_total_pushforward_integral_iff R FT XT beta hm set_val f hSource.1 _).1 hSource.
exact:(EFin_inj (measure_integral_unique
  (@radon_positive_compact_integral_laws R XT ambient hAmbient.1 hAmbient.2 f hF) hImage)).
Qed.
End CurrentAmbientVariationIntegral.
