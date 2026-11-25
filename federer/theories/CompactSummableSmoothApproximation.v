(** Federer (1969), 4.1.19, p. 377: recover
    the measurable derivative from its compact smooth
    probes. This supporting density step reuses the
    original-U L1 convolution limit of 4.1.18,
    p. 375, and realizes the same convolution
    as an actual compact smooth field on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentVectorSpaces CurrentCoefficientNorms
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothRestrictionUP SmoothRestrictionSealed
  CompactSummableMultivectors CompactSummableFieldIntegral
  CompactSummableMultivectorAmbient CompactSummableMultivectorAmbientAgreement
  CompactSummableMultivectorDifference CompactSummableMultivectorSmoothField
  CompactSummableOpenConvolution CompactSummableFullConvolution
  EuclideanClosedSupportTube EuclideanOpenDomainMeasure
  SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP
  SmoothingConvolutionExistence MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OriginalSmoothApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Z := (exterior_power X d).
Local Notation N := (@current_vector_mass R h2 n d).
Local Notation hN := (@current_vector_mass_real_norm R h2 n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation EF := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation WF := (@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation rawF := (@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation W := (@compact_summable_multivector_space R h2 n d U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation size := (@compact_summable_multivector_size R h2 n d U hU).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation support := (@compact_summable_multivector_ambient_support R h2 n d U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation phi := (@SmoothingKernel.value R n).
Local Notation family := (@SmoothingDilation.value R n phi).
Local Notation hPhi := (@SmoothingKernel.laws R n).
Local Notation hFamily := (@SmoothingDilation.laws R n phi).

(** Source for [compact_summable_smooth_approximation_on_carrier]:
    original compact smooth probes are dense in
    Omega for the actual original L1 cost,
    supporting almost uniqueness of the weak derivative
    in Federer 4.1.19, p. 377.
    The prescribed compact carrier contains only the
    printed positive tube; no common global bound
    or finite ambient volume is imposed. *)
Theorem compact_summable_smooth_approximation_on_carrier
    (xi : W) (delta : R) (K : smooth_compact_set hNX U) :
  0<delta ->
  @euclidean_closed_support_tube R n (support xi) delta `<=` smooth_compact_carrier K ->
  forall tolerance : R, 0<tolerance -> exists eta : E, exists zeta : W,
    @smooth_function_support R X Z NX hNX U E ev eta `<=` smooth_compact_carrier K /\
    value zeta=(fun x : UT => ev eta (set_val x)) /\ size (xi-zeta)<tolerance.
Proof.
move=> hDelta hTube tolerance hTolerance.
have [xiFull [P [hValue [hSize [hConvolution hLimit]]]]] :=
  @compact_summable_open_convolution_exists R h2 n d U hU phi family hPhi hFamily xi.
have hInside : @euclidean_closed_support_tube R n (support xi) delta `<=` U.
  exact: (subset_trans hTube (smooth_compact_in_domain K)).
have [r [hR hNear]] := @hLimit delta hDelta hInside tolerance hTolerance.
pose epsilon := Num.min delta r/2.
have hMin : 0<Num.min delta r by rewrite lt_min hDelta hR.
have hEpsilon : 0<epsilon by rewrite /epsilon divr_gt0 // ltr0n.
have hHalf : epsilon<Num.min delta r by rewrite /epsilon; lra.
have hMinDelta : Num.min delta r<=delta by rewrite ge_min lexx.
have hMinR : Num.min delta r<=r by rewrite ge_min lexx orbT.
have hEDelta := lt_le_trans hHalf hMinDelta.
have hER := lt_le_trans hHalf hMinR.
have [a [hA hSmall]] := @hNear epsilon hEpsilon hER.
have [hP hPOff] := @hConvolution epsilon hEpsilon.
have [f [hConv hImage]] := @compact_summable_full_convolution_exists R h2 n d
  phi family hPhi hFamily epsilon hEpsilon xiFull.
have hRaw := @compact_summable_multivector_full_ambient_agreement R h2 n d U hU
  xi xiFull hValue.
rewrite hRaw in hConv.
have hUnique := @smoothing_convolution_unique R n Z N hN (family epsilon)
  (raw xi) (rawF (P epsilon)) (fv f) hP hConv.
pose restriction := @SmoothRestriction.operator R X Z NX N hNX hN
  U Full hU (fun _ _ => Logic.I) E EF ev fv hE hF.
have hRestriction := @SmoothRestriction.laws R X Z NX N hNX hN
  U Full hU (fun _ _ => Logic.I) E EF ev fv hE hF.
pose eta := restriction f.
have hOff (x : X) (hx : U x) (hK : ~smooth_compact_carrier K x) : ev eta x=0.
  rewrite (@hRestriction f x hx) -hUnique.
  apply: (@hPOff x)=> hSupport.
  apply: hK; apply: (@hTube x).
  exact: (@euclidean_closed_support_tube_mono R n (support xi) (support xi)
    epsilon delta (fun _ h => h) (ltW hEDelta) x hSupport).
have hSupport : @smooth_function_support R X Z NX hNX U E ev eta
    `<=` smooth_compact_carrier K.
  apply: (smooth_function_compact_support_iff hE K eta).2=> x hx.
  have [hUx|hUx] := pselect (U x).
  - exact: (@hOff x hUx hx).
  - exact: (smooth_function_evaluation_outside hE eta hUx).
have [zeta hZeta] := @compact_summable_multivector_smooth_field R h2 n d
  U hU eta K hOff.
have hIntegral := @compact_summable_field_size_integral R UT Z N hN mu hMu (xi-zeta)%R.
have hFunction : (fun x : UT => N (value (xi-zeta)%R x))=
    (fun x : UT => N (rawF (P epsilon) (set_val x)-value xi x)).
  apply: funext=> x.
  rewrite compact_summable_multivector_value_difference hZeta
    (@hRestriction f (set_val x) (set_valP x)) -hUnique
    (real_seminorm_subtract hN.1).
  reflexivity.
rewrite hFunction in hIntegral.
have hExact : size (xi-zeta)%R=a := EFin_inj (measure_integral_unique hIntegral hA).
exists eta,zeta; split; first exact: hSupport.
split; first exact: hZeta.
by rewrite hExact.
Qed.
End OriginalSmoothApproximation.
