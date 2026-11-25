(** Federer (1969), 4.1.2, p. 347: the
    original compact smooth kernel has an actual
    Banach-valued convolution with every measurable locally
    norm-integrable field. The compact source bound is
    proved before applying the existing vector integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormClassOneUP NormRegularity
  VectorDaniellHypotheses GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence SmoothCompactSet PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  MeasureVectorIntegralUP SummableRealFunctionUP SummableRealArithmetic EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP SmoothingConvolutionUP CompactScalarKernelBound SmoothScalarKernelTranslation
  MeasurableScalarVectorProduct TotalVectorIntegralDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactSmoothConvolutionExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable f:X->Y.
Hypothesis hField:@is_locally_integrable_vector_field R X Y N NY hN hNY mu f.
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall z,r<N z ->psi z=0.

(** Source for [compact_smooth_convolution_at_exists]: the
    original vector integral exists at every centre,
    Federer 4.1.2, p. 347. Local
    norm integrability suffices on one compact ball;
    no global L1 hypothesis is added. *)
Theorem compact_smooth_convolution_at_exists x:
  exists y:Y,is_measure_vector_integral mu
    (partial_function_total (fun z=>(psi (x-z)*:f z:real_norm_metric_space hNY))) y.
Proof.
have [M [hM hBound]]:=@compact_scalar_kernel_bound_exists R n psi r
  (norm_class_continuous (hPsi 0%N)) hOff.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True) [set z|N (z-x)<=r]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN x r).
have [b hLocal]:=@locally_integrable_vector_compact_norm R X Y N NY hN hNY mu f hField K.
have hMeas:=@measurable_scalar_vector_product R X Y NY hNY mu hm
  (fun z=>psi (x-z)) f hSep
  (@smooth_scalar_kernel_translation_measurable R n psi hPsi x)
  (@locally_integrable_vector_measurable R X Y N NY hN hNY mu f hField).
pose majorant:=fun z=>if pselect (smooth_compact_carrier K z) then NY (f z) else 0.
have hMajorant:=@real_total_integral_scale R X mu hm majorant b M hLocal.
pose integrand:=fun z=>psi (x-z)*:f z.
have hDom z:NY (integrand z)<=M*majorant z.
  rewrite /integrand /majorant.
  case:(pselect (smooth_compact_carrier K z))=>hz.
  - rewrite (real_seminorm_scale hNY.1).
    exact:(ler_wpM2r (real_seminorm_nonnegative hNY.1 (f z)) (hBound (x-z))).
  - have hNo:~(N (z-x)<=r).
      move=>hSmall; apply:hz; exact hSmall.
    have hLarge:r<N (x-z).
      rewrite (real_seminorm_subtract hN.1 x z) ltNge; exact/negP.
    rewrite (@hOff (x-z) hLarge) scale0r (real_seminorm_zero hNY.1) mulr0.
    exact:lexx.
have [y [hy hUpper]]:=@dominated_total_vector_integral_exists R X Y NY hNY hY mu hm
  integrand (fun z=>M*majorant z) (M*b) hSep hMeas hMajorant hDom.
exists y; exact hy.
Qed.

(** Source for [compact_smooth_convolution_exists]: the
    original pointwise vector integrals form an actual
    convolution function, Federer 4.1.2, p. 347.
    Each value is specified independently by its integral. *)
Theorem compact_smooth_convolution_exists:
  exists g:X->Y,is_smoothing_convolution hNY psi f g.
Proof.
have [g hg]:=choice compact_smooth_convolution_at_exists.
exists g; exact hg.
Qed.
End CompactSmoothConvolutionExistence.
