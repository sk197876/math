(** Federer (1969), 3.2.13, p. 250: the
    recurrence Gamma(s+1)=s Gamma(s). Positive
    dyadic segments, the proved finite fundamental
    theorem, vanishing endpoint terms and dominated
    convergence establish the improper integration-by-parts step. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EulerGammaUP EulerGamma EulerGammaDerivativeIntegral EulerGammaPrimitiveDifferential
  EulerGammaPrimitiveSegmentIntegral EulerGammaPrimitiveEndpointBounds GammaDyadicExhaustion
  LebesgueScalarMeasure MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  SummableRealFunctionUP SummableRealArithmetic RealSubsetIntegralGraph RealDominatedIntegralLimit
  ExtendedRealOrderLimit RealErrorOrderLimit RealDifferenceOrderLimit ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gamma_primitive_dyadic_cutoff]: finite
    segment restrictions of the Gamma recurrence
    derivative, Federer 3.2.13, p. 250.
    This prescribed auxiliary is used only to
    pass from positive segments to the positive ray. *)
Definition gamma_primitive_dyadic_cutoff (R:realType) (s:R) n (x:R):R:=
  if ((1/2)^+n<=x<=2^+n) then euler_gamma_primitive_derivative s x else 0.

(** Source for [euler_gamma_recurrence]: the displayed
    identity Gamma(s+1)=s Gamma(s), s>0,
    in Federer 3.2.13, p. 250. Both
    Gamma values are the actual finite defining
    integrals; no endpoint decay or improper integral
    identity is an extra hypothesis. *)
Theorem euler_gamma_recurrence (R:realType) (s:R) (hs:0<s) (hs1:0<s+1):
  euler_gamma hs1=s*euler_gamma hs.
Proof.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose D:=gamma_completed_derivative s.
pose f:=gamma_primitive_dyadic_cutoff s.
pose c n:=euler_gamma_primitive s ((2:R)^+n)-euler_gamma_primitive s ((1/2)^+n).
have hD:=euler_gamma_completed_derivative_integral hs hs1.
have hSum:summable_real_functions mu D.
  exists (s*euler_gamma hs-euler_gamma hs1); exact hD.
have hH:=summable_real_absolute hm hSum.
have hHalf:0<(1/2:R) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<=1) by lra.
have hTwo1:1<=(2:R) by lra.
have hDom n x:`|f n x|<=`|D x|.
  rewrite /f /gamma_primitive_dyadic_cutoff; case:ifP=>hx; last by rewrite normr0; exact:normr_ge0.
  have hxPos:0<x:=lt_le_trans (exprn_gt0 n hHalf) (andP hx).1.
  by rewrite /D (@gamma_completed_derivative_on R s x hxPos).
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
      (gamma_completed_derivative_off s hxNot) subrr normr0.
have hI n:is_measure_integral mu (real_total_integrand (f n)) (c n)%:E.
  have hLow:0<(1/2:R)^+n:=exprn_gt0 n hHalf.
  have hOrder:((1/2:R)^+n<=(2:R)^+n).
    exact:le_trans (exprn_ile1 n (ltW hHalf) hHalf1) (exprn_ege1 n hTwo1).
  have hSegment:=euler_gamma_primitive_segment_integral s hLow hOrder.
  apply:((@real_subset_integral_total R R mu `[(1/2:R)^+n,(2:R)^+n]
    (euler_gamma_primitive_derivative s) (f n) (c n)%:E _ _).1 hSegment).
  - move=>x; rewrite /= in_itv /= =>hx; by rewrite /f /gamma_primitive_dyadic_cutoff hx.
  - move=>x hx; rewrite /f /gamma_primitive_dyadic_cutoff.
    case:ifP=>h; last by [].
    exfalso; apply:hx; by rewrite /= in_itv /=.
have hEndpoints:extended_order_limit (fun n=>(c n)%:E) (0%R)%:E.
  have hh:=real_difference_order_limit (@euler_gamma_primitive_tail_dyadic_limit R s)
    (euler_gamma_primitive_origin_dyadic_limit hs).
  by rewrite subrr in hh.
have hZero:=@real_dominated_integral_limit R R mu hm f D (fun x=>`|D x|) c 0
  hH hD.1 hDom hPoint hI hEndpoints.
have he:=measure_integral_unique hD hZero.
have hReal:s*euler_gamma hs-euler_gamma hs1=0:=EFin_inj he.
lra.
Qed.
