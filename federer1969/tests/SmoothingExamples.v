(** Federer (1969), 4.1.2, pp. 346-348: boundary regressions
    for the actual regularisation interface. Dimension zero
    preserves every input, scale one recovers the kernel, and
    empty domains retain actual test cutoff sequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealMetricBackground NormRegularity NormClassZeroTotalMeasurable
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext MeasureVectorIntegralUP MeasureVectorIntegralZero
  VectorDaniellHypotheses Smoothing SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smoothing_scale_one_regression]: substituting
    epsilon=1 in the original formula gives the original kernel,
    Federer 4.1.2, p. 346, including dimension zero. *)
Theorem smoothing_scale_one_regression (R:realType) n (phi:R_n R n->R)
    (family:R->R_n R n->R):
  is_smoothing_dilation phi family ->forall x,family 1 x=phi x.
Proof.
move=>hFamily x; rewrite (@hFamily 1 ltr01 x).
by rewrite expr1n invr1 scale1r mul1r.
Qed.

(** Source for [smoothing_zero_source_regression]: in R^0 the
    original unit-mass convolution is the identity for every
    separable normed target, supporting the zero-dimensional
    endpoint of Federer 4.1.2, pp. 346-347. *)
Theorem smoothing_zero_source_regression (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (hSep:is_separable_normed_space hNY)
    (phi:R_n R 0->R) (hPhi:is_smoothing_kernel phi)
    (family:R->R_n R 0->R) (hFamily:is_smoothing_dilation phi family)
    (e:R) (he:0<e) (f g:R_n R 0->Y):
  is_smoothing_convolution hNY (family e) f g ->g=f.
Proof.
move=>hConv; apply:funext=>x.
pose X:=R_n R 0.
pose N:=inner_norm (@euclidean_inner_productP R 0).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 0).
pose mu:=@euclidean_lebesgue_measure R 0.
pose hm:=euclidean_lebesgue_is_measure R 0.
have hUnique (a b:X):a=b by rewrite (@coordinate_zero R a) (@coordinate_zero R b).
have hSmooth:=@smoothing_dilation_smooth R 0 phi hPhi family hFamily e he.
have hMeas:=@norm_class_zero_scalar_real_measurable R X N hN mu hm
  (@euclidean_distribution_measure_open R 0) (family e) (norm_class_continuous (hSmooth 0%N)).
have hI:=@nonnegative_weighted_constant_vector_integral R X Y NY hNY mu hm (family e) 1 (f x)
  hSep hMeas (@smoothing_dilation_nonnegative R 0 phi hPhi family hFamily e he)
  (@smoothing_dilation_integral_one R 0 phi family hPhi hFamily e he).
rewrite scale1r in hI.
have hEq:(fun z:X=>(family e (x-z)*:f z:real_norm_metric_space hNY))=
    (fun z=>(family e z*:f x:real_norm_metric_space hNY)).
  apply:funext=>z; by rewrite (hUnique (x-z) z) (hUnique z x).
have h:=hConv x; rewrite hEq in h.
exact:measure_vector_integral_unique h hI.
Qed.

(** Source for [smoothing_zero_input_regression]: every original
    smoothing sends the zero input to zero, supporting the
    linear convolution and the zero-target endpoint of
    Federer 4.1.2, p. 347. *)
Theorem smoothing_zero_input_regression (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (psi:R_n R n->R) (g:R_n R n->Y):
  is_smoothing_convolution hNY psi (fun _=>0) g ->g=(fun _=>0).
Proof.
move=>hConv; apply:funext=>x.
have h:=hConv x.
have hEq:(fun z:R_n R n=>(psi (x-z)*:(0:Y):real_norm_metric_space hNY))=
    (fun _=>(0:real_norm_metric_space hNY)).
  apply:funext=>z; exact:scaler0.
rewrite hEq in h.
exact:(measure_vector_integral_unique h (@measure_vector_integral_zero R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n))).
Qed.

(** Source for [smoothing_empty_domain_cutoff_regression]: the
    actual zero tests form an admissible cutoff sequence on
    empty U, supporting the arbitrary-open endpoint of
    Federer 4.1.2, p. 348. *)
Theorem smoothing_empty_domain_cutoff_regression (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (E:lmodType R) (ev:E->X->R^o)
    (hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) set0 ev):
  @is_test_cutoff_exhaustion R X NX hNX set0 E ev hE (fun _=>0).
Proof.
move=>K; exists 1%N; split; first exact:ltn0Sn.
move=>j hj x hx; exfalso; exact:(smooth_compact_in_domain K x hx).
Qed.
