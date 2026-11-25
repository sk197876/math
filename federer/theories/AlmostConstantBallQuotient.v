(** Federer (1969), 4.1.7, p. 358:
    the exact original ball quotient of
    an almost constant scalar field is
    that constant at every point where
    all positive-radius balls have positive finite
    measure. This supporting statement applies the
    earlier characteristic integral and null-change laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology MetricClosedBalls TopologicalBorel
  PartialFunctionBasic PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP
  RadonBorelRegularity BorelRegularMeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality
  MeasureDensityTransfer CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  RealSubsetCharacteristicIntegral SummableRealFunctionUP SummableRealArithmetic BallIntegralQuotientLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [almost_constant_ball_quotient_everywhere]:
    exact scalar ball integrals give the
    original constant limit at every source
    point, supporting the orientation of E^n
    in Federer 4.1.7, p. 358.
    The positive finite ball hypothesis will
    be proved for the actual Lebesgue measure. *)
Theorem almost_constant_ball_quotient_everywhere (R:realType) (X:metricType R)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (f:X->R) (c:R):
  measure_almost_everywhere mu [set z|f z=c]->
  (forall x:X,forall r:R,0<r->exists b:R,mu (metric_closed_ball x r)=b%:E /\0<b)->
  forall x:X,is_ball_integral_quotient_limit mu (real_total_integrand f) x c.
Proof.
move=>hAgree hBalls x epsilon hEpsilon.
exists 1;split;first exact:ltr01.
move=>r hrPositive hrSmall.
have [b [hMass hB]]:=@hBalls x r hrPositive.
pose B:=metric_closed_ball x r.
pose chi:=@CharacteristicFunction.value R X B.
have hChi:=@CharacteristicFunction.laws R X B.
have hMeas:=@borel_regular_borel_measurable R X mu hm (radon_borel_regular hm hr)
  B (closed_borel_set (@metric_closed_ball_closed R X x r)).
have hIntegral:=@measure_characteristic_integral R X mu hm B chi hChi hMeas.
rewrite hMass in hIntegral.
have hScale:=@real_total_integral_scale R X mu hm chi b c hIntegral.
have hCommutative:(fun z=>c*chi z)=(fun z=>chi z*c) by apply:funext=>z;exact:mulrC.
rewrite hCommutative in hScale.
have hConstant:=(@real_subset_characteristic_integral R X mu B chi (fun _=>c) (c*b)%:E hChi).2 hScale.
have hAlmost:measure_almost_equal mu (real_total_integrand (fun _=>c)) (real_total_integrand f).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAgree)=>z hz.
  exists c%:E;split;by rewrite real_total_integrand_graph ?hz.
have hSubset:=@zero_extension_almost_equal R X (extended_real_line R) mu hm 0%E B
  (real_total_integrand (fun _=>c)) (real_total_integrand f) hAlmost.
have hActual:is_measure_subset_integral mu B (real_total_integrand f) (c*b)%:E.
  exact:(measure_integral_almost_equal hm hConstant hSubset).
exists (c*b),b;split;first exact:hMass.
split;first exact:hB.
split;first exact:hActual.
by rewrite mulfK ?gt_eqF // subrr normr0.
Qed.
