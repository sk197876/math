(** Federer (1969), 4.1.14, p. 371: differentiation commutes
    with smoothing, so a continuous almost-everywhere norm majorant
    bounds the differential of a sufficiently small smoothing.
    This supporting local-kernel estimate uses 4.1.2, p. 347,
    separately in each direction. It never integrates an operator field
    and imposes no separability premise on an operator space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormClassOneUP NormRegularity NormClassZeroWhole NormedCurveDerivativeUP
  NormDifferentialUP NormDifferentialDirectional GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanOwnNormCompleteness EuclideanNormCountableBase CountableBaseDenseSet
  VectorDaniellHypotheses LipschitzUP MetricLocalLipschitzContinuity
  ContinuousDualUP ContinuousDualNorm ContinuousDualSealed
  ContinuousBidualUP ContinuousBidualSealed FiniteContinuousReflexivity
  ReflexiveLocalDirectionalField SmoothingLocalLipschitzInput
  LocallyIntegrableVectorFieldUP SmoothingConvolutionExistence
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingDilationIntegral SmoothingConvolutionUP
  ContinuousSmoothingSmoothness NormedSmoothingSubstitution
  EuclideanLebesgueDimensions EuclideanReflectionTranslation CurrentMapDifferential
  EuclideanHomOperator HomSpaceTopology MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurePushforward UnitKernelVectorAlmostBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingAEDifferentialBound.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation mu:=(@euclidean_lebesgue_measure R n).
Local Notation hm:=(euclidean_lebesgue_is_measure R n).
Local Notation Op:=(@euclidean_operator_norm R n nu).
Local Notation YD:=(@ContinuousDual.space R Y NY hNY).
Local Notation ed:=(@ContinuousDual.evaluation R Y NY hNY).
Local Notation DN:=(@ContinuousDual.norm R Y NY hNY).
Local Notation hYD:=(@ContinuousDual.laws R Y NY hNY).
Local Notation hND:=(continuous_dual_norm_is_norm hYD).
Local Notation YB:=(@ContinuousDual.space R YD DN hND).
Local Notation eb:=(@ContinuousDual.evaluation R YD DN hND).
Local Notation BN:=(@ContinuousDual.norm R YD DN hND).
Local Notation hYB:=(@ContinuousDual.laws R YD DN hND).
Local Notation tau:=(@ContinuousBidual.value R Y YD YB NY hNY ed DN hYD eb BN hYB).
Local Notation hTau:=(@ContinuousBidual.laws R Y YD YB NY hNY ed DN hYD eb BN hYB).

(** Source for [smoothing_euclidean_target_separable]: the original
    Euclidean target is separable, by 2.7.16, pp. 134–135,
    supplying the target premise of 4.1.2, p. 347. This is not
    separability of a differential or operator space. *)
Let hSep:is_separable_normed_space hNY.
Proof.
have[B hB]:=@euclidean_norm_countable_open_base R nu.
exact:(@countable_open_base_dense_set (real_norm_metric_space hNY) 0 B hB).
Qed.

(** Source for [smoothing_euclidean_target_reflexive]: finite-dimensional
    normed targets are reflexive, Federer 2.4.12, p. 88, supplying
    only the original input differentiation premise of 4.1.2, p. 347. *)
Let hReflexive:is_reflexive_embedding tau.
Proof.
exact:(@finite_continuous_dual_reflexive R [the finType of 'I_nu] Y YD YB
  (@coordinate_basis R nu) (@coordinate_basisP R nu) NY hNY
  ed DN hYD eb BN hYB tau hTau).
Qed.

Variable F:X->Y.
Hypothesis hLocal:@is_locally_metric_lipschitz R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) setT F.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Variable g:X->Y.
Hypothesis hConvolution:is_smoothing_convolution hNY (family e) F g.
Variables (W:set X) (sigma:X->R^o).
Hypothesis hMajorant:measure_almost_everywhere mu
  [set x|W x->exists D:Hom X Y,
    has_norm_differential NX NY setT F x D /\ Op D<=sigma x].

(** Source for [smooth_convolution_ae_differential_bound]: the
    smoothed actual differential has norm at most M when the
    original almost-everywhere majorant is at most M on the
    translated nonzero kernel locus, Federer 4.1.14, p. 371.
    Only the original finite Euclidean target is used. *)
Theorem smooth_convolution_ae_differential_bound a M:
  0<=M ->
  (forall z,family e z!=0->W (a-z) /\ sigma (a-z)<=M) ->
    Op (@current_map_differential R n nu setT g a)<=M.
Proof.
move=>hM hLocus.
have hFContinuous:norm_class_zero NX NY setT F:=
  norm_continuous_whole_class_zero (metric_local_lipschitz_continuous_whole hLocal).
have hSmooth:=@continuous_smooth_convolution_smooth R n Y NY hNY
  (@euclidean_own_norm_complete R nu) F hFContinuous (family e) e g
  (@smoothing_dilation_smooth R n phi hPhi family hFamily e he)
  (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he)
  hConvolution.
pose Dg:=@current_map_differential R n nu setT g a.
have hActual:=@current_map_differential_actual R n nu setT g hSmooth a Logic.I.
apply:hom_operator_norm_least;first exact:hM.
move=>v.
have[xi [hRep [hZero [hField hAE]]]]:=@reflexive_local_directional_field_exists
  R n Y YD YB NY hNY (@euclidean_own_norm_complete R nu) hSep
  ed DN hYD eb BN hYB tau hTau hReflexive F hLocal v.
have[q hQ]:=@smoothing_convolution_exists R n Y NY hNY
  (@euclidean_own_norm_complete R nu) hSep phi hPhi family hFamily e he xi hField.
have hQLimit:=@smoothing_local_lipschitz_input_derivative R n Y NY hNY
  (@euclidean_own_norm_complete R nu) hSep phi hPhi family hFamily e he
  F xi g q hLocal v hRep hZero hAE hConvolution hQ a.
have hDLimit:=@norm_differential_directional_limit R X Y NX NY hNX hNY
  setT g a Dg hActual v.
have hEqual:Dg v=q a:=punctured_norm_limit_unique hNY hDLimit hQLimit.
rewrite hEqual.
have hTranslated:measure_almost_everywhere mu
    [set z|W (a-z)->exists D:Hom X Y,
      has_norm_differential NX NY setT F (a-z) D /\ Op D<=sigma (a-z)].
  have h:measure_almost_everywhere (measure_pushforward (fun z:X=>a-z) mu)
      [set x|W x->exists D:Hom X Y,
        has_norm_differential NX NY setT F x D /\ Op D<=sigma x].
    by rewrite euclidean_reflection_translation_measure.
  exact:h.
have hConullBound:measure_almost_everywhere mu
    [set z|family e z!=0->NY (xi (a-z))<=M*NX v].
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hTranslated)=>z hz hNonzero.
  have[hW hSigma]:=hLocus z hNonzero.
  have[D [hD hBound]]:=hz hW.
  have hLimit:=@norm_differential_directional_limit R X Y NX NY hNX hNY
    setT F (a-z) D hD v.
  rewrite (hRep (a-z) (D v) hLimit).
  have hNorm:=hom_operator_norm_bound
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R nu)
    (@coordinate_basisP R n) D v.
  exact:(le_trans hNorm (ler_wpM2r (real_seminorm_nonnegative hNX.1 v)
    (le_trans hBound hSigma))).
exact:(@unit_weight_vector_almost_bound R X Y NY hNY mu hm (family e)
  (fun z=>xi (a-z)) (q a) (M*NX v)
  (@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he)
  (@smoothing_dilation_integral_one R n phi family hPhi hFamily e he)
  (@normed_smoothing_convolution_alternate_integral R n Y NY hNY
    (family e) xi q hQ a) hConullBound).
Qed.
End SmoothingAEDifferentialBound.
