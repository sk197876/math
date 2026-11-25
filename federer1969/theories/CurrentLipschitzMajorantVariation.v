(** Federer (1969), 4.1.14, p. 371: for the original
    locally Lipschitz map and every continuous Lebesgue-AE
    differential majorant sigma, ||f#T|| is bounded on every
    set by f#(||T|| sigma^m). The proof smooths the original
    map near K, uses the defining approximation law, and
    takes the original variation integrals to their limit.
    No derivative hypothesis is imposed for ||T||-almost
    every point, and the flat input need not be normal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormScalarClassZeroTopology
  NormClassOneUP NormClassZeroTopology NormClassHigherRestriction NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet
  SmoothCompactInteriorThickening CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentMassSealed CurrentIntegrationCriterion CurrentFiniteMassRepresentation CurrentOpenRestriction
  CurrentOpenRestrictionMass CurrentOpenRestrictionVariation CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentProperSupportDomain CurrentMapDifferential EuclideanHomOperator
  NormalisedCurrentSealed FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardUP CurrentCompactLipschitzImageChosenApproximation
  CurrentFlatOpenRestriction CurrentFlatSequenceLimits CurrentSmoothApproximationUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationOriginal
  CurrentCompactMajorantApproximationUP CurrentCompactMajorantApproximationExistence
  CurrentAEMajorantLaws CurrentContinuousPushforwardWeight CurrentSmoothMajorantTestBound
  CurrentWeightedApproximationIntegralLimit CurrentWeakCompactTestBounds
  FunctionLatticeUP CompactSupportFunctionUP RadonCompactScalarIntegral
  DistributionVariationDomain SmoothFunctionSpaceUP SmoothTestSpaces
  MeasureUP MeasureDensity MeasurePushforward MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzMajorantVariation.
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
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation CU:=(@current_space R h2 n U hU m).
Local Notation CV:=(@current_space R h2 nu V hV m).
Variable T:CU.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Variable Q:CV.
Hypothesis hQ:@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K T Q.
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypothesis hMajorant:@is_current_ae_differential_majorant R n nu U f sigma.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation fU:=(@current_map_on_domain R n nu U V f hImage).
Local Notation weight:=(fun x:UT=>(sigma (set_val x))^+m:R^o).
Local Notation targetWeight:=(measure_pushforward fU
  (measure_with_density mu (real_total_integrand weight))).

(** Source for [current_lipschitz_image_majorant_variation]:
    the full all-set inequality of Federer 4.1.14, p. 371.
    The continuous Lebesgue-AE majorant is the original
    hypothesis. Representability of the candidate image is
    derived from its defining approximation law. The exact
    original source measure, degree zero, zero caps and
    empty source or target are retained. *)
Theorem current_lipschitz_image_majorant_variation:
  @is_integration_representable_current R h2 nu m V hV Q /\
  forall hRepresented:@is_integration_representable_current R h2 nu m V hV Q,
    forall B,(@NormalisedCurrent.measure R h2 nu m V hV Q hRepresented B
      <=targetWeight B)%E.
Proof.
have hFClass:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  U f hU hLocal.
have hSupport:=@flat_current_supported_support R h2 n m U hU K T hFlat.
have hCompact:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
have hProper:=@current_compact_map_proper R h2 n nu m U V hU T f hImage
  hFClass hCompact.
have hSigmaPositive:=@current_ae_differential_majorant_nonnegative R n nu
  U f sigma hSigma hMajorant.
have hSigmaContinuous:continuous (fun x:UT=>(sigma (set_val x):R^o)).
  exact:(@norm_class_zero_scalar_restriction_continuous R X NX hNX U sigma hSigma).
have hWeightContinuous:continuous weight.
  have hPower:forall k:nat,continuous (fun x:UT=>((sigma (set_val x))^+k:R^o)).
    elim=>[|k ih] x.
    - have hZero:(fun y:UT=>((sigma (set_val y))^+0:R^o))=
        (fun _:UT=>(1:R^o)).
        by apply:funext=>y;rewrite expr0.
      rewrite hZero.
      exact:(@cvg_cst R^o (1:R) UT (nbhs x) (@nbhs_filter UT x)).
    - have hExp:(fun y:UT=>(sigma (set_val y))^+k.+1)=
        (fun y:UT=>sigma (set_val y)*(sigma (set_val y))^+k).
        by apply:funext=>y;rewrite exprS.
      rewrite hExp.
      exact:(@cvgM R UT (nbhs x) (@nbhs_filter UT x)
        (fun y:UT=>sigma (set_val y))
        (fun y:UT=>(sigma (set_val y))^+k)
        (sigma (set_val x)) ((sigma (set_val x))^+k)
        (@hSigmaContinuous x) (@ih x)).
  exact:hPower m.
have hWeightPositive:forall x:UT,0<=weight x.
  move=>x;exact:(@exprn_ge0 R m (sigma (set_val x))
    (@hSigmaPositive (set_val x) (set_valP x))).
pose hTargetMeasure:=@current_continuous_pushforward_weight_measure R h2 n nu m
  U V hU T hT weight hWeightPositive f hImage.
pose hTargetRadon:=@current_continuous_pushforward_weight_radon R h2 n nu m
  U V hU hV T hT weight hWeightContinuous hWeightPositive f hImage hFClass hProper.
have[Z [g [eta hMajorantApprox]]]:=
  @current_compact_majorant_smooth_approximation_exists R n nu U V hU hV
    K f sigma hLocal hImage hSigma hMajorant.
have[L hApprox]:=current_compact_majorant_ordinary hMajorantApprox.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
pose hSFlat:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat.
pose hSCompact:=@flat_supported_current_compact R h2 n m Z hZ KZ S hSFlat.
have hSSupport:=@flat_current_supported_support R h2 n m Z hZ KZ S hSFlat.
have hSupportZ:forall x,@current_support R h2 n U hU m T x->Z x.
  move=>x hx;exact:hKZ x (hSupport x hx).
have hSRepresented:=@current_neighbourhood_restriction_representable R h2 n m
  Z U hZ hU hZU T hT hSupportZ.
have hSFinite:(@CurrentMass.value R h2 n m Z hZ S< +oo)%E.
  exact:le_lt_trans
    (@current_open_restriction_mass_bound R h2 n m Z U hZ hU hZU T) hFinite.
pose hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z g hApprox.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[radius [hRadius [E [hImageE hTube]]]]:=
  @smooth_compact_interior_thickening R Y NY hNY nu (@coordinate_basis R nu)
    (@coordinate_basisP R nu) V hV fK.
have hInterior:forall x,smooth_compact_carrier K x->
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  move=>x hx;exists radius;split;first exact:hRadius.
  move=>h hh;apply:(hTube (f x+h) (f x)).
  - change ((f @` smooth_compact_carrier K) (f x));by exists x.
  - rewrite [f x+h]addrC addrK;exact:ltW hh.
pose P:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S hSCompact.
have hFlatLimit:=@current_compact_lipschitz_image_chosen_approximation R h2 n nu m
  U V hU hV f hImage hLocal K T hFlat Q hQ L Z g hApprox E hInterior.
have hWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E P Q hFlatLimit.
have hImageZ:forall x,Z x->V (f x).
  move=>x hx;exact:hImage x (hZU x hx).
have hFZ:=@norm_class_zero_open_restriction R X Y NX NY U Z f hZU hZ hFClass.
have hSigmaZ:=@norm_class_zero_open_restriction R X R^o NX
  (fun t:R^o=>`|t|) U Z sigma hZU hZ hSigma.
have hError:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|eta i|<eps.
  move=>eps hEps;have[N hN]:=current_compact_majorant_error_zero hMajorantApprox hEps.
  exists N=>i hi.
  rewrite (ger0_norm (ltW (current_compact_majorant_error_positive hMajorantApprox i))).
  exact:hN i hi.
have hBounds h
    (hH:positive_function_lattice (@compactly_supported_continuous_functions R VT) h):
    exists a:nat->R,
      (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
        `|a i-@radon_positive_compact_integral R VT targetWeight
          hTargetMeasure hTargetRadon h|<eps) /\
      forall i,forall phi:@current_test_space R h2 nu V hV m,
        (forall y,@current_form_comass R h2 nu m
          (@current_test_value R h2 nu V hV m phi (set_val y))<=h y)->
        @current_value R h2 nu V hV m (P i) phi<=a i.
  have hOriginal:=@current_continuous_pushforward_weight_compact_integral R h2 n nu m
    U V hU hV T hT weight hWeightContinuous hWeightPositive
    f hImage hFClass hProper h hH.
  pose fZ:=@current_map_on_domain R n nu Z V f hImageZ.
  have hSmall:=(@current_neighbourhood_variation_total_integral_iff R h2 n m
    Z U hZ hU hZU T hT hSupportZ hSRepresented
    (fun x:UT=>h (fU x)*(sigma (set_val x))^+m) _).2 hOriginal.
  have hFunctions:
      (fun x:current_domain R n Z=>
        h (fU (@current_open_domain_inclusion R n Z U hZU x))*
          (sigma (set_val (@current_open_domain_inclusion R n Z U hZU x)))^+m)=
      (fun x:current_domain R n Z=>h (fZ x)*(sigma (set_val x))^+m).
    apply:funext=>x;congr (_*_);congr (h _);apply:val_inj;by [].
  rewrite hFunctions in hSmall.
  have[a [hA hLimit]]:=@current_weighted_approximation_integral_limit R h2 n nu m
    Z V hZ S hSRepresented hSFinite KZ hSSupport f hImageZ hFZ sigma hSigmaZ
    g (current_smooth_approximation_image hG) (current_smooth_approximation_class hG)
    (current_smooth_approximation_uniform hG) eta hError h _ hH hSmall.
  exists a;split;first exact:hLimit.
  move=>i phi hPhi.
  pose hp:=@current_compact_map_proper R h2 n nu m Z V hZ S (g i)
    (current_smooth_approximation_image hG i)
    (norm_class_continuous (current_smooth_approximation_class hG i 0%N)) hSCompact.
  have hDerivative:forall x,@current_support R h2 n Z hZ m S x->
      @euclidean_operator_norm R n nu (@current_map_differential R n nu Z (g i) x)
        <=sigma x+eta i.
    move=>x hx;exact:(@current_compact_majorant_differential_bound R n nu U V K
      f sigma Z g eta hMajorantApprox i x (hSSupport x hx)).
  exact:(@current_smooth_majorant_compact_test_bound R h2 n nu m Z V hZ hV
    S hSRepresented (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) hp (fun x=>sigma x+eta i)
    hDerivative h (a i) hH.2 (@hA i) phi hPhi).
split.
- exact:(@current_weak_limit_compact_bounds_representable R h2 nu m V hV
    P Q hWeak targetWeight hTargetMeasure hTargetRadon hBounds).
- move=>hRepresented.
  exact:(@current_weak_limit_compact_bounds_variation R h2 nu m V hV
    P Q hWeak targetWeight hTargetMeasure hTargetRadon hBounds hRepresented).
Qed.
End CurrentLipschitzMajorantVariation.
