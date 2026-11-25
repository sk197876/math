(** Federer (1969), 4.1.18, p. 375: the
    independently specified translated Radon average
    has its original weighted product integral.
    This law compares the independent scalar actions
    with the separately proved product witness; no
    opaque value is unfolded.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain EuclideanFullDomainMeasure ProductMeasure MeasureUP RadonMeasureUP
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP
  EuclideanKernelRadonAverageUP EuclideanKernelProductDensity EuclideanKernelRadonAverageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_kernel_radon_average_product_integral]:
    every original compact positive test integrates
    over the literal weighted product before addition,
    supporting 4.1.18, p. 375, by 2.6.2, p. 115.
    The theorem applies to any candidate satisfying the
    independent original translated-measure specification. *)
Theorem euclidean_kernel_radon_average_product_integral (R:realType) n
    (beta:set (current_domain R n (fun _=>True))->\bar R)
    (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta)
    (w:R_n R n->R^o)
    (hW:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) (fun _=>True) w)
    (hPositive:forall z,0<=w z) (r:R)
    (hOff:forall z,r<inner_norm (@euclidean_inner_productP R n) z->w z= 0)
    (nu:set (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))->\bar R)
    (hNu:@is_euclidean_kernel_radon_average R n beta hBeta hBetaRadon w nu)
    (f:real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)) ->R):
  positive_function_lattice (@compactly_supported_continuous_functions R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) f ->
  is_measure_integral
    (product_measure (@euclidean_full_domain_measure_laws R n).1 hBeta)
    (real_total_integrand (fun z:((current_domain R n (fun _=>True))*
        (current_domain R n (fun _=>True)))%type=>
      w (set_val z.1)*f (set_val z.2+set_val z.1)))
    (@radon_positive_compact_integral R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      nu hNu.1 hNu.2.1 f)%:E.
Proof.
move=>hF.
have hProduct:=@euclidean_kernel_radon_image_product_integral R n beta hBeta hBetaRadon
  w hW hPositive r hOff f hF.
have hOriginal:=@euclidean_kernel_radon_image_translation_integral R n beta hBeta hBetaRadon
  w hW hPositive r hOff f hF.
have hFormula:=hNu.2.2.
have hCandidate:=@hFormula hNu.1 hNu.2.1 f hF.
have hEqual:=measure_integral_unique hOriginal hCandidate.
by rewrite hEqual in hProduct.
Qed.
