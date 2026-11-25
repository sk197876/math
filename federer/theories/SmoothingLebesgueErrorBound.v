(** Federer (1969), 4.1.2, p. 347: the
    actual smoothing error is bounded by M epsilon^-n
    times the original ball integral of |f(z)-f(x)|.
    The kernel may be nonsymmetric, and the vector
    target remains an arbitrary separable Banach space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormRegularity VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness MetricClosedBalls
  PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral SummableRealFunctionUP SummableRealArithmetic
  MeasureVectorIntegralUP EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius SmoothingKernelScalarBound
  SmoothScalarKernelTranslation EuclideanReflectionTranslation InvariantRealIntegral WeightedConstantVectorIntegral
  TotalVectorIntegralArithmetic TotalVectorIntegralEstimate LocalVectorDistanceIntegral SmoothingConvolutionUP MeasurableDistanceTo.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingLebesgueErrorBound.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [smoothing_lebesgue_error_bound]: the original
    ball-integral smoothing estimate in Federer 4.1.2,
    p. 347, before applying the Lebesgue-point limit.
    The actual scalar and vector integral values are retained. *)
Theorem smoothing_lebesgue_error_bound (f g:X->Y) (e:R) (a:T) (M J:R):
  0<e ->(forall z,`|phi z|<=M) ->
  is_smoothing_convolution hNY (family e) f g ->
  is_measure_subset_integral mu (metric_closed_ball a e)
    (partial_distance_to (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) (f a)) J%:E ->
  NY (g a-f a)<=M/(e^+n)*J.
Proof.
move=>he hBound hConvolution hJ.
have hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hMeas:=@smooth_scalar_kernel_translation_measurable R n (family e) hSmooth a.
have hNonneg z:0<=family e (a-z).
  exact:(@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he (a-z)).
have hInv:=@euclidean_reflection_translation_involutive R n a.
have hMass:=@invariant_real_total_integral R X mu hm (fun z=>a-z) (family e) 1
  (can_inj hInv) (@euclidean_reflection_translation_measure R n a)
  (@smoothing_dilation_integral_one R n phi family hPhi hFamily e he).
have hConst:=@nonnegative_weighted_constant_vector_integral R X Y NY hNY mu hm
  (fun z=>family e (a-z)) 1 (f a) hSep hMeas hNonneg hMass.
rewrite scale1r in hConst.
have hError:=@total_vector_integral_subtract R X Y NY hNY mu hm
  (fun z=>family e (a-z)*:f z) (fun z=>family e (a-z)*:f a)
  (g a) (f a) (hConvolution a) hConst.
have hNorm:is_measure_integral mu (real_total_integrand
    (fun z=>if pselect (metric_closed_ball a e z) then NY (f z-f a) else 0)) J%:E.
  apply:(measure_integral_graph_equivalent _ hJ)=>z y.
  exact:(@total_norm_distance_subset_graph R X Y NY hNY (metric_closed_ball a e) f (f a) z y).
have hMajorant:=@real_total_integral_scale R X mu hm
  (fun z=>if pselect (metric_closed_ball a e z) then NY (f z-f a) else 0) J (M/(e^+n)) hNorm.
apply:(@total_vector_integral_dominated_norm R X Y NY hNY mu hm
  (fun z=>family e (a-z)*:f z-family e (a-z)*:f a) (g a-f a)
  (fun z=>M/(e^+n)*(if pselect (metric_closed_ball a e z) then NY (f z-f a) else 0))
  (M/(e^+n)*J) hError hMajorant)=>z.
rewrite -scalerBr (real_seminorm_scale hNY.1).
case:(pselect (metric_closed_ball a e z))=>hz.
- exact:(ler_wpM2r (real_seminorm_nonnegative hNY.1 (f z-f a))
    (@smoothing_dilation_absolute_bound R n phi family M hFamily hBound e he (a-z))).
- have hZero:family e (a-z)=0.
    apply/eqP; apply/negPn/negP=>hNonzero.
    have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he (a-z) hNonzero.
    exfalso; apply:hz; change (is_true (N (a-z)<=e)); exact:ltW hRadius.
  by rewrite hZero normr0 mul0r mulr0.
Qed.
End SmoothingLebesgueErrorBound.
