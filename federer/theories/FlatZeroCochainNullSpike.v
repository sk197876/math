(** Federer (1969), 4.1.19, p. 377: an
    actual zero-cochain test of the distinction between
    arbitrary measurable representatives and the literal global
    comass defined in 4.1.7, p. 358. The
    representing pair has the original two actions
    and weak equation; a null singleton changes
    its global comass while the cochain stays zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing PairingLinear CurrentDomain
  CurrentCoefficientNorms CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentLonePairImageUP CurrentLonePairFlatSealed FlatCurrentUnionSpace
  FlatCochainSpace FlatCochainNormLaws FlatCochainPairFunctional
  FlatCochainRepresentationUP CompactSummableMultivectors
  EuclideanLebesgueDimensions ApproximateDifferentialAffine
  EuclideanOpenDomainMeasure EuclideanFullDomainMeasure
  MeasureUP MeasurePushforward MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality PartialFunctionBasic MeasurableNormedFunctionUP
  MeasurableNormedBasic MeasureIntegralUP MeasureConullZeroIntegral
  SummableRealFunctionUP NullSpikeZeroForm BoundedCurrentFormZero
  CurrentWeakExteriorPairUP WeakExteriorPairGraphAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ActualZeroCochainSpike.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation UT := (current_domain R 1%N Full).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 1%N d).
Local Notation hN d := (@current_form_comass_real_norm R h2 1%N d).
Local Notation P := (@current_lone_pair_space R h2 1%N 0%N Full hFull).
Local Notation Q := (@CurrentLonePairFlat.map R h2 1%N 0%N Full hFull).
Local Notation A := (@flat_cochain_space R h2 1%N 0%N Full hFull).
Local Notation F := (@flat_cochain_norm R h2 1%N 0%N Full hFull).
Local Notation value d := (@compact_summable_multivector_value R h2 1%N d Full hFull).
Local Notation mu := (@euclidean_open_domain_measure R 1%N Full).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R 1%N Full hFull)).

(** Source for [flat_zero_cochain_null_spike]:
    the actual representative test for the converse
    norm sentence in Federer 4.1.19, p. 377.
    Both displayed representation actions hold for the
    actual original zero cochain and opaque q;
    the weak equation holds too. The literal
    pointwise global-comass formula nevertheless fails for
    this arbitrary bounded measurable representative. *)
Theorem flat_zero_cochain_null_spike :
  exists phi : X -> Y 0%N, exists psi : X -> Y 1%N,
    @is_flat_cochain_pair_density R h2 1%N 0%N Full hFull Q (0:A)
      (fun x : UT => phi (set_val x))
      (fun x : UT => psi (set_val x)) /\
    @is_weak_current_exterior_pair R h2 1%N 0%N Full hFull
      (fun x : UT => phi (set_val x))
      (fun x : UT => psi (set_val x)) /\
    F (0:A)=0 /\
    @CurrentGlobalComass.value R h2 1%N 0%N Full phi= 1%:E /\
    (F (0:A))%:E <>
      Order.max (@CurrentGlobalComass.value R h2 1%N 0%N Full phi)
        (@CurrentGlobalComass.value R h2 1%N 1%N Full psi).
Proof.
pose phi := @null_spike_zero_form R 1%N (0:X).
pose psi := fun _ : X => (0:Y 1%N).
pose p := @euclidean_full_domain_point R 1%N.
pose a : UT := p 0.
have hNull : mu [set a]=0%E.
  change (@euclidean_full_domain_measure R 1%N [set a]=0%E).
  rewrite euclidean_full_domain_measure_image /measure_pushforward.
  have hSet : p @^-1` [set a]=[set (0:X)].
    apply/seteqP; split.
    - move=> x hx.
      have h := congr1 (set_val : UT -> X) hx.
      exact: h.
    - move=> x hx; change (x=0) in hx.
      by rewrite hx.
  rewrite hSet; exact: (@positive_euclidean_singleton_null R 0%N (0:X)).
have hAlmost : measure_almost_everywhere mu
    [set x : UT | (0:Y 0%N)=phi (set_val x)].
  have hConull : measure_almost_everywhere mu (~` [set a]).
    by rewrite /measure_almost_everywhere setCK.
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hConull)=> x hx.
  have hPoint : set_val x<>(0:X).
    move=> hX; apply: hx; apply: val_inj; exact: hX.
  exact: esym (@null_spike_zero_form_off_point R 1%N (0:X) (set_val x) hPoint).
have hPartial : measure_almost_equal mu
    (partial_function_total (fun _ : UT => (0:real_norm_metric_space (hN 0%N))))
    (partial_function_total (fun x : UT =>
      (phi (set_val x):real_norm_metric_space (hN 0%N)))).
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hAlmost)=> x hx.
  exists (0:Y 0%N); split; first exact: erefl.
  exact: esym hx.
have hPhiMeas := @measurable_normed_almost_equal R UT (Y 0%N)
  (N 0%N) (hN 0%N) mu hMu _ _
  (@measurable_normed_total_constant R UT (Y 0%N) (N 0%N) (hN 0%N) mu hMu 0)
  hPartial.
have hGlobal : @CurrentGlobalComass.value R h2 1%N 0%N Full phi= 1%:E.
  exact: (@null_spike_zero_form_global_comass R h2 1%N (0:X)).
have hCap (x : UT) : N 0%N (phi (set_val x))<=1.
  apply: ((@current_global_comass_bound R h2 1%N 0%N Full phi 1).1 _
    (set_val x) Logic.I).
  by rewrite hGlobal.
have hPhiBounded : @is_bounded_measurable_current_form R h2 1%N Full 0%N
    (fun x : UT => phi (set_val x)).
  split; first exact: hPhiMeas.
  exists 1; split; first exact: ler01.
  exact: hCap.
have hPsiBounded := @bounded_measurable_current_form_zero R h2 1%N 1%N Full hFull.
have hDensity : @is_lone_pair_form_density R h2 1%N 0%N Full hFull
    (0:Hom P R^o) (fun x : UT => phi (set_val x))
    (fun x : UT => psi (set_val x)).
  split; first exact: hPhiBounded.
  split; first exact: hPsiBounded.
  split.
  - move=> xi; rewrite hom_zeroE.
    apply: (@measure_almost_zero_integral R UT mu hMu).
    apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hAlmost)=> x hx.
    apply/real_total_integrand_graph.
    change ((pairing_right (value 0%N xi x) (phi (set_val x)))%:E=0%E).
    by rewrite -hx linear0.
  - move=> eta; rewrite hom_zeroE.
    apply: (@measure_almost_zero_integral R UT mu hMu).
    apply: (@measure_almost_everywhere_mono R UT mu hMu setT _ _
      (measure_almost_everywhere_true hMu))=> x _.
    apply/real_total_integrand_graph.
    change ((pairing_right (value 1%N eta x) 0)%:E=0%E).
    by rewrite linear0.
have hZeroDensity : @is_flat_cochain_pair_density R h2 1%N 0%N Full hFull
    Q (0:A) (fun x : UT => phi (set_val x))
    (fun x : UT => psi (set_val x)).
  rewrite /is_flat_cochain_pair_density flat_cochain_pair_functional_zero.
  exact: hDensity.
have hWeak : @is_weak_current_exterior_pair R h2 1%N 0%N Full hFull
    (fun x : UT => phi (set_val x)) (fun x : UT => psi (set_val x)).
  apply: ((@weak_exterior_pair_graph_action_iff R h2 1%N 0%N Full hFull
    (0:Hom P R^o) (fun x : UT => phi (set_val x))
    (fun x : UT => psi (set_val x)) hDensity).2).
  by move=> v _; rewrite hom_zeroE.
have hZeroNorm : F (0:A)=0 := real_seminorm_zero
  (@flat_cochain_norm_is_norm R h2 1%N 0%N Full hFull).1.
exists phi,psi; split; first exact: hZeroDensity.
split; first exact: hWeak.
split; first exact: hZeroNorm.
split; first exact: hGlobal.
move=> hEquality.
have hLower : (@CurrentGlobalComass.value R h2 1%N 0%N Full phi <=
    Order.max (@CurrentGlobalComass.value R h2 1%N 0%N Full phi)
      (@CurrentGlobalComass.value R h2 1%N 1%N Full psi))%E.
  by rewrite le_max lexx.
rewrite hGlobal in hLower.
rewrite hZeroNorm hGlobal in hEquality.
rewrite -hEquality lee_fin in hLower.
have hBad := lt_le_trans (@ltr01 R) hLower.
by rewrite ltxx in hBad.
Qed.
End ActualZeroCochainSpike.
