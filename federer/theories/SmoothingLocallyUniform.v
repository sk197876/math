(** Federer (1969), 4.1.2, p. 347: for
    continuous f the smoothing converges locally uniformly.
    The proof uses compact-base uniform continuity,
    the original positive kernel and its actual mass one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormClassOneUP NormRegularity
  VectorDaniellHypotheses GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet CompactNearbyUniformContinuity EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  NormClassZeroTotalMeasurable SmoothingConvolutionUP SmoothingConvolutionSubstitution UnitKernelVectorError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingLocallyUniform.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable f:X->Y.
Variable g:R->X->Y.
Hypothesis hConvolution:forall e:R,0<e ->is_smoothing_convolution hNY (family e) f (g e).

(** Source for [smoothing_continuous_locally_uniform]: the original
    locally uniform convergence assertion of Federer 4.1.2,
    p. 347. The compact set and
    target error are arbitrary, and the bound holds
    simultaneously at every point of that compact set. *)
Theorem smoothing_continuous_locally_uniform:
  norm_class_zero N NY (fun _=>True) f ->
  forall K:smooth_compact_set hN (fun _=>True),forall eta:R,0<eta ->
  exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    forall a,smooth_compact_carrier K a ->NY (g e a-f a)<eta.
Proof.
move=>hContinuous K eta hEta.
have hEta2:0<eta/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hUniform]]:=@norm_class_zero_compact_uniform_nearby R X Y N NY hN hNY
  (fun _=>True) (smooth_compact_carrier K) f (smooth_compact_is_compact K)
  (fun _ _=>Logic.I) hContinuous (eta/2) hEta2.
exists d; split=>// e he hSmall a ha.
have hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hMeas:=@norm_class_zero_scalar_real_measurable R X N hN
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (@euclidean_distribution_measure_open R n) (family e) (norm_class_continuous (hSmooth 0%N)).
have hNonneg:=@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he.
have hMass:=@smoothing_dilation_integral_one R n phi family hPhi hFamily e he.
have hIntegral:=@smoothing_convolution_alternate_integral R n Y NY hNY (family e) f (g e)
  hSep (@hConvolution e he) a.
have hOscillation z:family e z!=0 ->NY (f (a-z)-f a)<=eta/2.
  move=>hz.
  have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he z hz.
  have hNear:N ((a-z)-a)<d.
    have hDiff:(a-z)-a = -z by rewrite addrAC subrr add0r.
    rewrite hDiff (real_seminorm_negate hN.1); exact:(lt_trans hRadius hSmall).
  exact:ltW (hUniform a (a-z) ha Logic.I hNear).
have hBound:=@unit_weight_vector_error_bound R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (family e) (fun z=>f (a-z)) (g e a) (f a) (eta/2)
  hSep hMeas hNonneg hMass hIntegral hOscillation.
apply:le_lt_trans hBound _; lra.
Qed.
End SmoothingLocallyUniform.
