(** Federer 2.10.2, p. 171, real-dimensional normalization and its
    consistency in degree zero; supporting evaluation of the actual
    defining Gamma integral. Also supports 3.2.13, pp. 250–251. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EulerGammaUP EulerGamma EulerGammaDerivativeIntegral EulerGammaPrimitiveDifferential
  EulerGammaPrimitiveSegmentIntegral EulerGammaPrimitiveEndpointBounds GammaDyadicExhaustion
  LebesgueScalarMeasure MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  SummableRealFunctionUP SummableRealArithmetic RealSubsetIntegralGraph RealDominatedIntegralLimit
  ExtendedRealOrderLimit RealErrorOrderLimit RealDifferenceOrderLimit ExtendedRealOrderTopology EulerGammaRecurrence
  EulerGammaFinite EulerGammaMeasurable RealExponentialOrderLimit RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_gamma_one]: Federer 2.10.2, p. 171,
    the Gamma normalization in degree zero. The actual positive-ray
    integral of exp(-x) is one, by the proved finite fundamental theorem,
    dyadic exhaustion and endpoint limits. No value at Gamma(0) is used. *)
Theorem euler_gamma_one (R:realType) (hOne:(0:R)<1):
  euler_gamma hOne = 1.
Proof.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose D:=gamma_completed_derivative (0:R).
pose f:=gamma_primitive_dyadic_cutoff (0:R).
pose c n:=euler_gamma_primitive (0:R) ((2:R)^+n)-euler_gamma_primitive (0:R) ((1/2)^+n).
have hGamma:=euler_gamma_completed_integral hOne.
have hD : is_measure_integral mu (real_total_integrand D) (-euler_gamma hOne)%:E.
  have hScaled := @real_total_integral_scale R R mu hm
    (gamma_positive_completion (1:R)) (euler_gamma hOne) (-1) hGamma.
  have hFun : (fun x:R => -1*gamma_positive_completion (1:R) x)=D.
    apply:funext=>x; rewrite /D /gamma_completed_derivative add0r mul0r sub0r mulN1r.
    by [].
  by rewrite hFun mulN1r in hScaled.
have hSum:summable_real_functions mu D.
  exists (-euler_gamma hOne); exact hD.
have hH:=summable_real_absolute hm hSum.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<=1) by lra.
have hTwo1:1<=(2:R) by lra.
have hDom n x:`|f n x|<=`|D x|.
  rewrite /f /gamma_primitive_dyadic_cutoff; case:ifP=>hx; last by rewrite normr0; exact:normr_ge0.
  have hxPos:0<x:=lt_le_trans (exprn_gt0 n hHalf) (andP hx).1.
  by rewrite /D (@gamma_completed_derivative_on R 0 x hxPos).
have hPoint x:extended_order_limit (fun n=>(f n x)%:E) (D x)%:E.
  apply:real_error_extended_order_limit=>e he.
  case:(ltP 0 x)=>hx.
  - have [N hN]:=gamma_dyadic_segments_exhaust_positive hx.
    exists N=>n hn; by rewrite /f /gamma_primitive_dyadic_cutoff (hN n hn) /D gamma_completed_derivative_on // subrr normr0.
  - exists 0%N=>n _.
    have hNot:~~((1/2:R)^+n<=x<=2^+n).
      apply/negP=>/andP[hLow _].
      have hxPos:0<x:=lt_le_trans (exprn_gt0 n hHalf) hLow.
      by move:hxPos; rewrite ltNge hx.
    have hxNot:~0<x by move=>h; by move:h; rewrite ltNge hx.
    by rewrite /f /gamma_primitive_dyadic_cutoff (negbTE hNot) /D
      (gamma_completed_derivative_off (0:R) hxNot) subrr normr0.
have hI n:is_measure_integral mu (real_total_integrand (f n)) (c n)%:E.
  have hLow:0<(1/2:R)^+n:=exprn_gt0 n hHalf.
  have hOrder:((1/2:R)^+n<=(2:R)^+n).
    exact:le_trans (exprn_ile1 n (ltW hHalf) hHalf1) (exprn_ege1 n hTwo1).
  have hSegment:=euler_gamma_primitive_segment_integral (0:R) hLow hOrder.
  apply:((@real_subset_integral_total R R mu `[(1/2:R)^+n,(2:R)^+n]
    (euler_gamma_primitive_derivative (0:R)) (f n) (c n)%:E _ _).1 hSegment).
  - move=>x; rewrite /= in_itv /= =>hx; by rewrite /f /gamma_primitive_dyadic_cutoff hx.
  - move=>x hx; rewrite /f /gamma_primitive_dyadic_cutoff.
    case:ifP=>h; last by [].
    exfalso; apply:hx; by rewrite /= in_itv /=.
have hOrigin : extended_order_limit
    (fun n=>(euler_gamma_primitive (0:R) ((1/2)^+n))%:E) (1:R)%:E.
  have hInput : extended_order_limit (fun n=>(-((1/2:R)^+n))%:E) (0:R)%:E.
    apply:real_error_extended_order_limit=>e he.
    have hq:0<(1/2:R)<1 by apply/andP; split; lra.
    have [N hN] := geometric_uniform_tail hq (ler01 : (0:R)<=1) he.
    exists N=>n hn.
    have hpos : 0 <= (1/2:R)^+n := exprn_ge0 n (ltW hHalf).
    rewrite subr0 normrN (ger0_norm hpos).
    have hh:=hN n hn; by rewrite mulr1 in hh.
  have hh := real_exponential_order_limit hInput.
  rewrite (real_exponential_zero (RealExponential.laws R)) in hh.
  have hFun : (fun n => (euler_gamma_primitive (0:R) ((1/2)^+n))%:E)=
      (fun n => (RealExponential.exponential (-((1/2:R)^+n)))%:E).
    by apply:funext=>n; rewrite /euler_gamma_primitive real_power_zero_exponent mul1r.
  rewrite hFun; exact hh.
have hEndpoints:extended_order_limit (fun n=>(c n)%:E) (-1:R)%:E.
  have hh:=real_difference_order_limit (@euler_gamma_primitive_tail_dyadic_limit R 0) hOrigin.
  by rewrite sub0r in hh.
have hZero:=@real_dominated_integral_limit R R mu hm f D (fun x=>`|D x|) c (-1)
  hH hD.1 hDom hPoint hI hEndpoints.
have he:=measure_integral_unique hD hZero.
have hReal: -euler_gamma hOne= -1:=EFin_inj he.
lra.
Qed.
