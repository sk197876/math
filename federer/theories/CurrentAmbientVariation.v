(** Federer (1969), 4.1.18, p. 375: view the
    original variation of a full-space current on the
    ambient R^n by the canonical inclusion. The original
    Radon measure and scalar-test gauge are preserved
    exactly.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom AlternatingForms RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  FiniteNormEquivalence CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed NormalisedDistributionRepresentationUP
  DistributionIntegrationRepresentationUP DistributionVariationUP DistributionVariationDomain
  EuclideanFullDomainMeasure EuclideanFullDomainCompactFunctions
  CompactSupportFunctionUP FunctionLatticeUP RadonCompactScalarIntegral
  IsotropyGroupTopology ProperMapUP RadonProperPushforward
  MeasureUP MeasurePushforward RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  RadonWeightedPushforwardIntegral SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAmbientVariation.
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
Local Notation point:=(@euclidean_full_domain_point R n).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation values:=(smooth_test_values_hom hE).
Local Notation dvalues:=(@distribution_domain_values R XT Full Y DT values).
Variable T:@current_space R h2 n Full hFull m.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Local Notation action:=(@current_value R h2 n Full hFull m T).
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m Full hFull T hT).
Local Notation hNorm:=(@NormalisedCurrent.laws R h2 n m Full hFull T hT).
Local Notation hRep:=(normalised_distribution_representation_laws hNorm).
Local Notation hm:=(distribution_representation_measure hRep).
Local Notation hr:=(distribution_representation_radon hRep).

(** Source for [current_ambient_variation]: the original
    ||T|| on the actual ambient R^n, supporting
    the translations of variation in 4.1.18, p. 375.
    This is only an image along inverse domain copies. *)
Definition current_ambient_variation:set XT->\bar R:=
  measure_pushforward (set_val:FT->XT) mu.
Local Notation ambient:=current_ambient_variation.

(** Source for [current_ambient_variation_laws]: the
    canonical ambient copy is still the original
    Radon variation, supporting Federer 4.1.18, p. 375.
    Infinite total variation remains allowed. *)
Theorem current_ambient_variation_laws:
  is_measure ambient /\is_radon_measure ambient.
Proof.
have hProper:@is_proper_map FT XT set_val.
  move=>K hK.
  have hCompact:compact (point @` K).
    apply:continuous_compact hK.
    exact:continuous_subspaceT (@euclidean_full_domain_point_continuous R n).
  have hEqual:(point @` K)=(set_val @^-1` K:set FT).
    apply:funext=>x;apply:propext;split.
    - by move=>[y hy <-].
    - move=>hx;exists (set_val x);first exact:hx.
      apply:val_inj;reflexivity.
  by rewrite -hEqual.
split;first exact:measure_pushforward_is_measure hm.
exact:(@proper_continuous_radon_pushforward R FT XT mu hm hr set_val
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) NX hNX)
  (@set_type_val_continuous XT Full) hProper).
Qed.
Local Notation D:=(@radon_positive_compact_integral R XT ambient
  current_ambient_variation_laws.1 current_ambient_variation_laws.2).

(** Source for [current_ambient_variation_original_gauge]:
    the ambient Radon integral is exactly the original
    scalar-test variation gauge, supporting the upper/lower
    weak variation bounds in 4.1.18, p. 375. *)
Theorem current_ambient_variation_original_gauge f:
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_distribution_variation_value NY values action f (D f)%:E.
Proof.
move=>hF.
have hFullF:positive_function_lattice (@compactly_supported_continuous_functions R FT)
    (fun x:FT=>f (set_val x)).
  split;first exact:euclidean_full_compact_function_pullback hF.1.
  by move=>x;exact:hF.2 (set_val x).
have [b [hGauge hIntegral]]:=normalised_distribution_original_gauge hNorm hFullF.
have hValues:distribution_variation_values NY dvalues action
    (fun x:FT=>f (set_val x))=distribution_variation_values NY values action f.
  apply:funext=>a;apply:propext;split.
  - move=>[omega [hOmega hValue]];exists omega;split=>// x.
    exact:hOmega (point x).
  - move=>[omega [hOmega hValue]];exists omega;split=>// x.
    exact:hOmega (set_val x).
rewrite /is_distribution_variation_value hValues in hGauge.
have hAmbient:=(@real_total_pushforward_integral_iff R FT XT mu hm
  (set_val:FT->XT) f hIntegral.1 b%:E).1 hIntegral.
have hActual:=@radon_positive_compact_integral_laws R XT ambient
  current_ambient_variation_laws.1 current_ambient_variation_laws.2 f hF.
have hEqual: D f=b.
  exact:(EFin_inj (measure_integral_unique hActual hAmbient)).
by rewrite hEqual.
Qed.
End CurrentAmbientVariation.
