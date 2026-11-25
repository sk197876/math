(** Actual-space endpoint regressions for Federer (1969),
    4.1.14, pp. 371–372: the nonzero R^0
    point and distinct constant endpoint maps with
    original derivative majorant sigma=0. The actual
    affine chain is the unit interval and has
    mass one. Apply the final original mass
    theorem and evaluate its literal source variation
    integral. The degree-zero power 0^0 is one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormDifferentialLinear NormClassOneUP NormClassZeroArithmetic
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential
  EuclideanHomOperator LipschitzUP LipschitzBasic LipschitzConstant
  CurrentDomain CurrentSpaces CurrentBoundary CurrentDirac DiracCurrentBounds
  CurrentDiracRadonRepresentation CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMassSealed CurrentMassBasic CurrentMassFiniteAlgebra CurrentCompactTopUniqueness
  CurrentSegmentMapUP ScalarSegmentCoordinateValues OrientedSegmentCurrentSealed
  OrientedSegmentCurrentBoundary OrientedSegmentNormal OrientedSegmentMass
  CurrentCompactElementaryPushforwards CurrentCompactPushforwardAlgebra
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentFlatLipschitzPushforwardSealed
  CurrentCompactLipschitzPushforwardSmooth CurrentLipschitzAffineChainSealed
  CurrentLipschitzAffineHomotopyFormula CurrentLipschitzAffineChainMass
  EuclideanLebesgueDimensions MeasureAlmostUP MeasureAlmostBasic
  CurrentCompactMajorantApproximationUP SummableRealFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness PointMassMeasure PointMassIntegral.
From FedererTests Require Import FlatCurrentEndpointExamples AffineCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzAffineChainEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 0%N).
Local Notation Y:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U:=(fun _:X=>True).
Local Notation V:=(fun _:Y=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hV:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation one:=(@euclidean_one_embed R 1).
Local Notation f:=(fun _:X=>(0:Y)).
Local Notation g:=(fun _:X=>one).
Local Notation sigma:=(fun _:X=>(0:R^o)).
Local Notation image:=(fun (x:X) (_:True)=>Logic.I).
Local Notation hf:=(fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (0:Y) k hU).
Local Notation hg:=(fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U one k hU).
Local Notation T:=(@dirac_current R h2 0%N U hU (0:X)).
Local Notation K:=(@flat_point_singleton_index R).
Local Notation hKT:=(@zero_dimensional_point_flat R h2).
Local Notation hCompactT:=(@flat_supported_current_compact R h2 0%N 0%N
  U hU K T hKT).
Local Notation interval_domain:=(@scalar_segment_full_domain R 0 1).
Local Notation interval:=(@OrientedSegmentCurrent.value R h2 1%N V hV
  (@euclidean_one_embed R 0) one interval_domain).

(** Source for [lipschitz_affine_endpoint_constant_local]:
    the original constant endpoint maps are locally
    Lipschitz, by 2.2.7, p. 64, supporting
    Federer 4.1.14, pp. 371–372. *)
Local Lemma lipschitz_affine_endpoint_constant_local (a:Y):
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U (fun _:X=>a).
Proof.
apply:metric_lipschitz_is_local.
exact:(metric_lipschitz_of_bound
  (least_metric_lipschitz_bound (@metric_lipschitz_constant_map R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U a))).
Qed.

(** Source for [lipschitz_affine_endpoint_point_flat]:
    the actual point current belongs to the
    original compact-index flat union, by 4.1.12,
    p. 368, supporting 4.1.14, pp. 371–372. *)
Local Lemma lipschitz_affine_endpoint_point_flat:
  @is_flat_current R h2 0%N 0%N U hU T.
Proof. by exists K;exact:hKT. Qed.
Local Notation hFlat:=lipschitz_affine_endpoint_point_flat.
Local Notation hFLocal:=(lipschitz_affine_endpoint_constant_local (0:Y)).
Local Notation hGLocal:=(lipschitz_affine_endpoint_constant_local one).
Local Notation hBand:=(fun (t:R) (x:X) (_:0<=t<= 1)
  (_:@current_support R h2 0%N U hU 0%N T x)=>Logic.I).
Local Notation chain:=(@CurrentLipschitzAffineChain.value R h2 0%N 1%N 0%N
  U V hU hV f g hFLocal hGLocal T hFlat hBand).
Local Notation weight:=(fun x:current_domain R 0%N U=>
  NY (g (set_val x)-f (set_val x))*(sigma (set_val x))^+0%N).

(** Source for [lipschitz_affine_endpoint_global_point_image]:
    each final opaque global flat image sends
    the actual R^0 point to the corresponding
    target point, supporting 4.1.14, pp. 370–371.
    The old smooth point-image law determines it. *)
Local Lemma lipschitz_affine_endpoint_global_point_image (a:Y)
    (hLocal:@is_locally_metric_lipschitz R (real_norm_metric_space hNX)
      (real_norm_metric_space hNY) U (fun _:X=>a)):
  @CurrentFlatLipschitzPushforward.value R h2 0%N 1%N 0%N
    U V hU hV (fun _:X=>a) image hLocal T hFlat=
  @dirac_current R h2 1%N V hV a.
Proof.
pose ha:=fun k=>@norm_class_constant R X Y NX NY hNX hNY U a k hU.
have hSmooth:=@current_compact_lipschitz_image_smooth R h2 0%N 1%N 0%N
  U V hU hV (fun _:X=>a) image hLocal K T hKT ha _
  ((@CurrentFlatLipschitzPushforward.laws R h2 0%N 1%N 0%N
    U V hU hV (fun _:X=>a) image hLocal T hFlat).2 K hKT).
apply:(eq_trans hSmooth).
exact:(@current_compact_map_dirac_image R h2 0%N 1%N U V hU hV
  (fun _:X=>a) image ha (0:X) Logic.I hCompactT).
Qed.

(** Source for [lipschitz_affine_zero_majorant_chain_is_interval]:
    the actual final affine chain of the
    nonzero R^0 point is the nonzero unit
    interval, testing Federer 4.1.14, pp. 371–372.
    Use the final original homotopy identity and
    preceding compact positive-top-degree boundary uniqueness. *)
Example lipschitz_affine_zero_majorant_chain_is_interval:chain=interval.
Proof.
have hFormula:=@current_lipschitz_affine_homotopy_zero_formula R h2 0%N 1%N
  U V hU hV f g image image hFLocal hGLocal T hFlat hBand.
rewrite (lipschitz_affine_endpoint_global_point_image hFLocal)
  (lipschitz_affine_endpoint_global_point_image hGLocal) in hFormula.
have[L hL]:=(@CurrentLipschitzAffineChain.laws R h2 0%N 1%N 0%N
  U V hU hV f g hFLocal hGLocal T hFlat hBand).1.
have hCompactChain:=@flat_supported_current_compact R h2 1%N 1%N V hV L chain hL.
have hNormalInterval:=@oriented_segment_current_normal R h2 1%N V hV
  (@euclidean_one_embed R 0) one interval_domain.
apply:(@current_compact_top_boundary_unique R h2 1%N 0%N V hV
  chain interval hCompactChain hNormalInterval.2 (erefl 1%N)).
have hZero:(@euclidean_one_embed R 0)=(0:Y).
  apply/ffunP=>i;by rewrite /euclidean_one_embed ffunE.
rewrite (@oriented_segment_current_boundary R h2 1%N V hV
  (@euclidean_one_embed R 0) one interval_domain) hZero.
exact:esym hFormula.
Qed.

(** Source for [lipschitz_affine_zero_majorant_original_integral]:
    every representation witness gives the same
    literal original variation integral, equal to one,
    for the sigma=0 and m=0 endpoint of
    Federer 4.1.14, p. 372. The original
    point variation is used without a chosen extension. *)
Example lipschitz_affine_zero_majorant_original_integral
    (hT:@is_integration_representable_current R h2 0%N 0%N U hU T):
  measure_lower_integral (@NormalisedCurrent.measure R h2 0%N 0%N U hU T hT)
    (real_total_integrand weight)= 1%:E.
Proof.
rewrite (@current_dirac_variation R h2 0%N U hU (0:X) Logic.I hT).
pose c:=@current_dirac_domain_point R 0%N U (0:X) Logic.I.
have hIntegral:=@point_mass_real_integral R (current_domain R 0%N U) c weight.
have hValue:=measure_lower_integral_unique
  (measure_lower_integral_specification _ (real_total_integrand weight)) hIntegral.2.2.
change (measure_lower_integral (PointMassMeasure.point_mass R c)
  (real_total_integrand weight)=(NY (one-0)*(0:R)^+0%N)%:E) in hValue.
rewrite hValue expr0 mulr1 subr0 euclidean_one_norm_coordinate
  /euclidean_one_embed ffunE normr1.
by [].
Qed.

(** Source for [lipschitz_affine_endpoint_zero_differential]:
    both constant endpoint maps have actual zero
    differential, proving the printed Lebesgue-AE
    majorant premise of Federer 4.1.14, p. 371.
    No arbitrary total derivative extension is used. *)
Local Lemma lipschitz_affine_endpoint_zero_differential (a:Y):
  @is_current_ae_differential_majorant R 0%N 1%N U (fun _:X=>a) sigma.
Proof.
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R 0%N)
  (euclidean_lebesgue_is_measure R 0%N) setT _ _
  (@measure_almost_everywhere_true R X (@euclidean_lebesgue_measure R 0%N)
    (euclidean_lebesgue_is_measure R 0%N)))=>x _ hx.
exists (0:Hom X Y);split.
- exact:(@norm_differential_constant R X Y NX NY hNX hNY U x a (hU x hx)).
- by rewrite (real_seminorm_zero (@euclidean_operator_norm_is_norm R 0%N 1%N).1).
Qed.

(** Source for [lipschitz_affine_zero_majorant_sharp_bound]:
    the final original sigma bound gives exactly
    one for the actual nonzero affine chain,
    verifying the degree-zero exponent in Federer
    4.1.14, pp. 371–372. A power sigma
    instead of sigma^0 would give a false zero bound. *)
Example lipschitz_affine_zero_majorant_sharp_bound:
  T<>0 /\(0:R)^+0%N = 1 /\chain<>0 /\
  @CurrentMass.value R h2 1%N 1%N V hV chain= 1%:E /\
  forall hT:@is_integration_representable_current R h2 0%N 0%N U hU T,
    measure_lower_integral (@NormalisedCurrent.measure R h2 0%N 0%N U hU T hT)
      (real_total_integrand weight)= 1%:E /\
    (@CurrentMass.value R h2 1%N 1%N V hV chain<=
      measure_lower_integral (@NormalisedCurrent.measure R h2 0%N 0%N U hU T hT)
        (real_total_integrand weight))%E.
Proof.
have hMass:@CurrentMass.value R h2 1%N 1%N V hV chain= 1%:E.
  rewrite lipschitz_affine_zero_majorant_chain_is_interval
    (@oriented_segment_current_mass R h2 1%N V hV
      (@euclidean_one_embed R 0) one interval_domain).
  have hZero:(@euclidean_one_embed R 0)=(0:Y).
    apply/ffunP=>i;by rewrite /euclidean_one_embed ffunE.
  by rewrite hZero subr0 euclidean_one_norm_coordinate
    /euclidean_one_embed ffunE normr1.
split;first exact:(@affine_zero_dimensional_point_nonzero R h2).
split;first by rewrite expr0.
split.
- move=>hZero;rewrite hZero current_mass_zero in hMass.
  have hBad:(0:R)= 1:=EFin_inj hMass.
  by have:=@oner_neq0 R;rewrite -hBad eqxx.
split;first exact:hMass.
move=>hT;split;first exact:lipschitz_affine_zero_majorant_original_integral.
pose hSigma:=@norm_class_zero_constant R X R^o NX (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R) U 0 hU.
exact:((@current_lipschitz_affine_chain_mass R h2 0%N 1%N 0%N
  U V hU hV f g image image hFLocal hGLocal sigma hSigma
  (lipschitz_affine_endpoint_zero_differential (0:Y))
  (lipschitz_affine_endpoint_zero_differential one) T hFlat
  (@dirac_current_finite_mass R h2 0%N U hU (0:X) Logic.I).2 hBand).2 hT).
Qed.
End LipschitzAffineChainEndpointExamples.
