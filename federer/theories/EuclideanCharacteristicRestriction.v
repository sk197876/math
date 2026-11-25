(** Federer (1969), 4.1.8, p. 362: the
    coordinate-oriented characteristic-density current is
    the original measurable restriction of E^n.
    Use the proved original Euclidean variation,
    its almost-everywhere coordinate density and the
    original restriction's literal subset action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers AlternatingForms
  AlternatingPairing CurrentSpaces CurrentDensityUP CurrentEvaluation CurrentDomain CurrentIntegrationCriterion CurrentMeasurableRestriction
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentVariation EuclideanFullDomainMeasure
  EuclideanFullDomainSubsetIntegral EuclideanCharacteristicCurrent EuclideanLebesgueDimensions OpenSubspaceMeasure
  ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanCharacteristicRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Local Notation FT := (current_domain R n (fun _=>True)).
Local Notation E := (@euclidean_fundamental_current R h2 n).
Local Notation hE := (@euclidean_fundamental_current_representable R h2 n).
Local Notation mu := (@NormalisedCurrent.measure R h2 n n (fun _=>True) hFull E hE).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n n (fun _=>True) hFull E hE).
Local Notation hRep := (@NormalisedCurrent.laws R h2 n n (fun _=>True) hFull E hE).
Local Notation hMu := (distribution_representation_measure (normalised_distribution_representation_laws hRep)).
Local Notation top := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Variable B:set X.
Hypothesis hB:measure_measurable Leb B.
Local Notation A := ((set_val:FT->X) @^-1` B).

(** Source for [euclidean_restriction_set_measurable]: the
    original Euclidean-measurable set is measurable for
    the actual variation of E^n on its full
    domain, supporting Federer 4.1.8, p. 362. *)
Lemma euclidean_restriction_set_measurable:measure_measurable mu A.
Proof.
rewrite (@euclidean_fundamental_current_variation R h2 n hE).
exact:(@open_subspace_preimage_measurable R NT (fun _=>True) Leb B hB).
Qed.

(** Source for [euclidean_fundamental_restricted_current]: the
    actual original E^n contracted B using the
    existing measurable restriction, supporting Federer
    4.1.8, p. 362. *)
Definition euclidean_fundamental_restricted_current:@full_current_space R h2 n n:=
  @current_measurable_restriction R h2 n n (fun _=>True) hFull E hE A
    euclidean_restriction_set_measurable.

(** Source for [euclidean_fundamental_restricted_action]: the
    original E^n contracted B evaluates every actual
    top-degree test by its coordinate-oriented integral
    over B, supporting Federer 4.1.8, p. 362.
    The canonical auxiliary density is replaced only
    on its proved null exceptional set. *)
Theorem euclidean_fundamental_restricted_action phi:
  is_measure_subset_integral Leb B (real_total_integrand (fun x=>pairing top
      (@current_test_value R h2 n (fun _=>True) hFull n phi x)))
    (@current_value R h2 n (fun _=>True) hFull n euclidean_fundamental_restricted_current phi)%:E.
Proof.
pose value:=@current_test_value R h2 n (fun _=>True) hFull n phi.
pose a:=@current_value R h2 n (fun _=>True) hFull n euclidean_fundamental_restricted_current phi.
have hOriginal:is_measure_subset_integral mu A
    (real_total_integrand (fun x:FT=>pairing (eta x) (value (set_val x)))) a%:E.
  exact:(@current_measurable_restriction_action R h2 n n (fun _=>True) hFull E hE A
    euclidean_restriction_set_measurable phi).
have hEta:=@euclidean_fundamental_current_auxiliary_constant R h2 n hE.
have hAgreement:measure_almost_equal mu
    (partial_function_zero_extension (0:extended_real_line R) A
      (real_total_integrand (fun x:FT=>pairing (eta x) (value (set_val x)))))
    (partial_function_zero_extension (0:extended_real_line R) A
      (real_total_integrand (fun x:FT=>pairing top (value (set_val x))))).
  apply:(@measure_almost_everywhere_mono R FT mu hMu _ _ _ hEta)=>x hx.
  have hValue:eta x=top:=hx.
  case:(pselect (A x))=>hAx.
  - exists (pairing top (value (set_val x)))%:E;split;
      apply/partial_function_zero_extension_graph;left;split=>//;
      by rewrite real_total_integrand_graph ?hValue.
  - exists 0%E;split;apply/partial_function_zero_extension_graph;right;by split.
have hTop:=measure_integral_almost_equal hMu hOriginal hAgreement.
rewrite (@euclidean_fundamental_current_variation R h2 n hE) in hTop.
exact:(@euclidean_full_domain_subset_integral_iff R n B (fun x=>pairing top (value x)) a%:E).2 hTop.
Qed.

(** Source for [euclidean_characteristic_current_restriction]: the
    actual characteristic-density current equals the
    original measurable restriction E^n contracted B,
    supporting the literal notation in Federer
    4.1.8, p. 362. *)
Theorem euclidean_characteristic_current_restriction:
  @euclidean_characteristic_current R h2 n B hB=euclidean_fundamental_restricted_current.
Proof.
apply:(@current_values_extensional R h2 n n (fun _=>True) hFull)=>phi.
exact:(EFin_inj (measure_integral_unique
  (@euclidean_characteristic_current_action R h2 n B hB phi)
  (euclidean_fundamental_restricted_action phi))).
Qed.

(** Source for [euclidean_characteristic_current_representable]: the
    actual restricted coordinate current is representable
    by integration, supporting the product use in
    Federer 4.1.8, p. 362. *)
Theorem euclidean_characteristic_current_representable:
  @is_integration_representable_current R h2 n n (fun _=>True) hFull
    (@euclidean_characteristic_current R h2 n B hB).
Proof.
rewrite euclidean_characteristic_current_restriction.
exact:(@current_measurable_restriction_representable R h2 n n (fun _=>True) hFull E hE A
  euclidean_restriction_set_measurable).
Qed.
End EuclideanCharacteristicRestriction.
