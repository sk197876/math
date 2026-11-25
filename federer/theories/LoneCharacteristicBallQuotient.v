(** Federer (1969), 4.1.5, p. 350:
    the numerator in the ball formula is
    the actual L1 extension evaluated on
    the characteristic function times y.
    Its membership and equality with the
    scalar subset integral are proved here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric MetricClosedBalls TopologicalBorel
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureLpMembershipUP MeasureVectorCharacteristicIntegral MeasureVectorIntegralUP CharacteristicFunctionUP
  CharacteristicFunctionSealed AbstractDualCharacteristicPairing DualLoneIntegralUP BallIntegralQuotientLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lone_characteristic_ball_quotient]: the exact
    original S(b_(x,r)y) numerator and its
    positive-radius limit in Federer 4.1.5,
    p. 350. Every displayed numerator
    belongs to the original L1 domain. *)
Theorem lone_characteristic_ball_quotient (R:realType) (X:metricType R)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (I:partial_function X (real_norm_metric_space hNY)->R)
    (hI:@is_dual_lone_integral R X Y NY hNY D ed xi mu I) (x:X) (y:Y) (l:R):
  is_ball_integral_quotient_limit mu
    (SummableRealFunctionUP.real_total_integrand (fun z=>ed (xi z) y)) x l ->
  forall eta:R,0<eta ->exists d:R,0<d /\forall r:R,0<r ->r<d ->
    exists mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass /\
      is_measure_lp_function mu 1 (partial_function_total
        (fun z=>((@CharacteristicFunction.value R X (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY))) /\
      `|I (partial_function_total
        (fun z=>((@CharacteristicFunction.value R X (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY)))/mass-l|<eta.
Proof.
move=>hLimit eta hEta.
have[d [hD hClose]]:=hLimit eta hEta.
exists d; split=>// r hR hSmall.
have[J [mass [hMass [hMassPositive [hIntegral hError]]]]]:=hClose r hR hSmall.
pose B:=metric_closed_ball x r.
pose s:=@CharacteristicFunction.value R X B.
have hS:=@CharacteristicFunction.laws R X B.
have hBMeasurable:=@borel_regular_borel_measurable R X mu hm (radon_borel_regular hm hr)
  B (@TopologicalBorel.closed_borel_set X B (@metric_closed_ball_closed R X x r)).
have hMember:=(@measure_vector_characteristic_integral R X Y NY hNY mu hm B s mass y hS hBMeasurable hMass).1.
have hActual:=@hI (partial_function_total (fun z=>(s z*:y:real_norm_metric_space hNY))) hMember.
have hActualSubset:=measure_integral_graph_equivalent
  (@abstract_dual_characteristic_pairing_graph R X Y D ed xi B s hS y) hActual.
have hEqual:=measure_integral_unique hActualSubset hIntegral.
have hNumerator:I (partial_function_total (fun z=>(s z*:y:real_norm_metric_space hNY)))=J by injection hEqual.
exists mass; split=>//; split=>//; split; first exact hMember.
by rewrite hNumerator.
Qed.
