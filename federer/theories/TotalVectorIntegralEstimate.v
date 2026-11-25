(** Federer (1969), 4.1.2, p. 347: an
    actual vector integral is bounded by any finite
    integrable scalar majorant of its norm. This
    uses the original L1 norm and scalar domination. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  VectorDaniellPairingMeasurability MeasureUP MeasureVectorIntegralUP MeasureVectorIntegralBound MeasureIntegralUP
  SummableRealFunctionUP SummableRealArithmetic TotalVectorIntegralDomination TotalVectorNormIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [total_vector_integral_dominated_norm]: the
    norm estimate used in the convolution difference
    and Taylor error, Federer 4.1.2, p. 347.
    Neither a finite ambient measure nor target
    completeness is required once the integral is given. *)
Theorem total_vector_integral_dominated_norm (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (f:X->Y) (y:Y) (g:X->R) (b:R):
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) y ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  (forall x,N (f x)<=g x) ->N y<=b.
Proof.
move=>hI hg hDom.
have hMeas:=@total_vector_norm_integrand_measurable R X Y N hN mu hm f hI.1.2.1.1.
have hBound x:`|N (f x)|<=g x.
  rewrite (ger0_norm (real_seminorm_nonnegative hN.1 (f x))); exact:hDom.
have [a [hNorm hA]]:=real_total_dominated_integral hm hMeas hg hBound.
have hValue:=@total_vector_lone_norm_value R X Y N hN mu hm f a hI.1.2.1.1 hNorm.
have hNBound:=@measure_vector_integral_norm_bound R X Y N hN mu hm _ y hI.
rewrite hValue lee_fin in hNBound.
exact:(le_trans hNBound (le_trans (ler_norm a) hA)).
Qed.
