(** Federer (1969), 4.1.5, p. 350: a
    nonnegative unit-mass smoothing kernel preserves
    a uniform norm bound. The earlier actual integral
    difference estimate supplies the assertion, including
    infinite ambient Lebesgue measure and dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions PartialFunctionBasic MeasureVectorIntegralUP MeasureVectorIntegralZero
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationNonzeroRadius SmoothingDilationSmooth SmoothingDilationIntegral
  SmoothingConvolutionUP NormedSmoothingSubstitution UnitKernelVectorDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_uniform_norm_bound]: the
    original uniform eta bound used for
    Phi_e*(w-h w) in Federer 4.1.5,
    p. 350. No new integrability assumption is
    added to the actual convolution premise. *)
Theorem smoothing_uniform_norm_bound (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (phi:R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (family:R->R_n R n->R)
    (hFamily:is_smoothing_dilation phi family) e (u g:R_n R n->Y) eta:
  0<e ->is_smoothing_convolution hNY (family e) u g ->
  (forall z,NY (u z)<=eta) ->forall x,NY (g x)<=eta.
Proof.
move=>he hConvolution hBound x.
have hIntegral:=@normed_smoothing_convolution_alternate_integral R n Y NY hNY (family e) u g hConvolution x.
have hZero:is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z:R_n R n=>(family e z*:(0:Y):real_norm_metric_space hNY))) 0.
  have hEq:(fun z:R_n R n=>(family e z*:(0:Y):real_norm_metric_space hNY))=
      (fun _:R_n R n=>(0:real_norm_metric_space hNY)).
    apply:funext=>z; exact:scaler0.
  rewrite hEq; exact:(@measure_vector_integral_zero R (R_n R n) Y NY hNY
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)).
have h:=@unit_weight_vector_difference_bound R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (family e) (fun z=>u (x-z)) (fun _=>0) (g x) 0 eta
  (@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he)
  (@smoothing_dilation_integral_one R n phi family hPhi hFamily e he)
  hIntegral hZero (fun z _=>ltac:(rewrite subr0; exact:hBound)).
by rewrite subr0 in h.
Qed.
