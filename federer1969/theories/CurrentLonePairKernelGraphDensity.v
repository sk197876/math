(** Federer (1969), 4.1.18, p. 377:
    every original q-zero pair is a
    J-limit of the compact smooth graph
    pairs on its original open U.
    Use the original ordinary pair convolution,
    its exact graph identity and its joint L1 limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet CompactSummableMultivectors CompactSummableMultivectorAmbient
  CompactSummableMultivectorAmbientAgreement CompactSummableMultivectorDifference
  CompactSummableFullConvolution CompactSummablePairConvolutionLone
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairCost
  CurrentLonePairAmbientKernel CurrentLonePairSmoothKernel
  CurrentCompactSmoothDivergenceUP CurrentFullSmoothGraphOpenRestriction
  CurrentCompactClosedTubeInside EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm
  SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP
  EuclideanOpenDomainMeasure MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section KernelGraphDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation FT := (current_domain R n Full).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation Pairs := (@current_lone_pair_space R h2 n m U hU).
Local Notation fullPairs := (@current_lone_pair_space R h2 n m Full hFull).
Local Notation raw d := (@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation rawF d := (@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation fieldSupport d :=
  (@compact_summable_multivector_ambient_support R h2 n d U hU).
Local Notation VN d := (@current_vector_mass R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation q := (@CurrentLonePair.map R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).

(** Source for [current_lone_pair_kernel_graph_dense]:
    the reverse inclusion in the printed
    kernel-closure identity of Federer 4.1.18,
    p. 377. Every positive J-error
    admits an actual original compact smooth
    graph pair. All natural degrees, empty
    carriers and arbitrary original open U remain allowed. *)
Theorem current_lone_pair_kernel_graph_dense (v : Pairs) :
  q v=0 -> forall tolerance : R, 0 < tolerance ->
  exists w : Pairs,
    @is_current_compact_smooth_divergence_pair R h2 n m U hU w /\
    J (v-w)%R < tolerance.
Proof.
move=> hZero tolerance hTolerance.
pose L := fieldSupport m v.1 `|` fieldSupport m.+1 v.2.
have hFirstSupport := @compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1.
have hSecondSupport := @compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2.
have hLCompact : @compact XT L := compactU hFirstSupport.1 hSecondSupport.1.
have hLU : L `<=` U.
  move=> x [hx|hx].
  - exact: (hFirstSupport.2.1 x hx).
  - exact: (hSecondSupport.2.1 x hx).
pose K0 := @Build_smooth_compact_set R X NX hNX U L hLU hLCompact.
have [delta [hDelta hInside]] := @current_compact_closed_tube_inside_exists R n U hU K0.
pose K := @Build_smooth_compact_set R X NX hNX U
  (@euclidean_closed_support_tube R n L delta) hInside
  (@euclidean_closed_support_tube_norm_compact R n L delta hLCompact).
pose phi := @SmoothingKernel.value R n.
pose hPhi := @SmoothingKernel.laws R n.
pose family := @SmoothingDilation.value R n phi.
pose hFamily := @SmoothingDilation.laws R n phi.
have [xiFull [hXiValue hXiSize]] :=
  @compact_summable_multivector_ambient_representative R h2 n m U hU v.1.
have [etaFull [hEtaValue hEtaSize]] :=
  @compact_summable_multivector_ambient_representative R h2 n m.+1 U hU v.2.
have hXiRaw := @compact_summable_multivector_full_ambient_agreement R h2 n m U hU
  v.1 xiFull hXiValue.
have hEtaRaw := @compact_summable_multivector_full_ambient_agreement R h2 n m.+1 U hU
  v.2 etaFull hEtaValue.
pose vFull : fullPairs := (xiFull,etaFull).
have hFullZero := @current_lone_pair_ambient_kernel R h2 n m U hU
  v vFull hXiValue hEtaValue hZero.
have [P [Q [hConvolutions hLimit]]] := @compact_summable_pair_convolution_lone
  R h2 n m U hU phi family hPhi hFamily v delta hDelta hInside.
have [d [hD hNear]] := @hLimit tolerance hTolerance.
pose epsilon := Num.min delta d/2.
have hMin : 0 < Num.min delta d by rewrite lt_min hDelta hD.
have hEpsilon : 0 < epsilon by rewrite /epsilon divr_gt0 // ltr0n.
have hHalf : epsilon < Num.min delta d by rewrite /epsilon; lra.
have hMinDelta : Num.min delta d <= delta by rewrite ge_min lexx.
have hMinD : Num.min delta d <= d by rewrite ge_min lexx orbT.
have hEDelta := lt_le_trans hHalf hMinDelta.
have hED := lt_le_trans hHalf hMinD.
have [hP [hQ [hPOff hQOff]]] := @hConvolutions epsilon hEpsilon.
have [a [hA hSmall]] := @hNear epsilon hEpsilon hED.
have [f [hF hFImage]] := @compact_summable_full_convolution_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon xiFull.
have [g [hG hGImage]] := @compact_summable_full_convolution_exists R h2 n m.+1
  phi family hPhi hFamily epsilon hEpsilon etaFull.
have hFOriginal := hF; rewrite hXiRaw in hFOriginal.
have hGOriginal := hG; rewrite hEtaRaw in hGOriginal.
have hFValues := @smoothing_convolution_unique R n (exterior_power X m) (VN m)
  (hVN m) (family epsilon) (raw m v.1) (rawF m (P epsilon)) (fv m f) hP hFOriginal.
have hGValues := @smoothing_convolution_unique R n (exterior_power X m.+1) (VN m.+1)
  (hVN m.+1) (family epsilon) (raw m.+1 v.2) (rawF m.+1 (Q epsilon))
  (fv m.+1 g) hQ hGOriginal.
have hGraph := @current_lone_pair_full_smooth_kernel R h2 n m phi family
  hPhi hFamily epsilon hEpsilon vFull f g hFullZero hF hG.
have hGCompactOff x : ~smooth_compact_carrier K x -> fv m.+1 g x=0.
  move=> hx; rewrite -hGValues.
  apply: (@hQOff x)=> hTube.
  apply: hx.
  exact: (@euclidean_closed_support_tube_mono R n
    (fieldSupport m.+1 v.2) L epsilon delta (fun _ h => or_intror h)
    (ltW hEDelta) x hTube).
have [w [hW [hFirst hSecond]]] := @current_full_smooth_graph_open_restriction
  R h2 n m U hU f g K hGraph hGCompactOff.
exists w; split; first exact: hW.
have hCost := @current_lone_pair_cost_integral R h2 n m U hU (v-w)%R.
have hFunction : (fun x : UT =>
    VN m (value m (((v-w)%R).1) x)+VN m.+1 (value m.+1 (((v-w)%R).2) x))=
    (fun x : UT =>
      VN m (rawF m (P epsilon) (set_val x)-value m v.1 x)+
      VN m.+1 (rawF m.+1 (Q epsilon) (set_val x)-value m.+1 v.2 x)).
  apply: funext=> x.
  change (VN m (value m (v.1-w.1)%R x)+
    VN m.+1 (value m.+1 (v.2-w.2)%R x)=
    VN m (rawF m (P epsilon) (set_val x)-value m v.1 x)+
    VN m.+1 (rawF m.+1 (Q epsilon) (set_val x)-value m.+1 v.2 x)).
  rewrite !compact_summable_multivector_value_difference hFirst hSecond
    -hFValues -hGValues
    (real_seminorm_subtract (hVN m).1)
    (real_seminorm_subtract (hVN m.+1).1).
  reflexivity.
rewrite hFunction in hCost.
have hEqual : J (v-w)%R=a := EFin_inj (measure_integral_unique hCost hA).
by rewrite hEqual.
Qed.
End KernelGraphDensity.
