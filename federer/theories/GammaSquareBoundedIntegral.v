(** Federer (1969), 3.2.13, p. 250: the actual bounded
    square substitution, using 3.2.6 rather than presupposing an
    improper change-of-variables theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground GammaSquareTargetMultiplicity GammaSquareSourceGraph
  EulerGammaMeasurable EulerGammaDerivativeIntegral EulerGamma ScalarSquareAbsoluteContinuity
  ScalarAbsoluteContinuousArea ScalarCurveRemainderNull LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel CountableOrderIntervals IntervalBumpFunctions
  MeasureUP MeasureIntegralUP MeasureIntegralSplitting MeasureSubsetIntegral
  RealSubsetIntegralGraph MeasureIntegralGraphEquivalence PartialFunctionUP PartialFunctionBasic
  SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gamma_square_target_integral_exists]: restrictions
    of the finite defining Gamma integral give the target
    integrals of the bounded square substitutions, Federer
    3.2.13, p. 250. *)
Lemma gamma_square_target_integral_exists (R:realType) (s b:R) (hs:(0<s)%R):
  exists a,is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (gamma_square_target_cutoff s b)) a.
Proof.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose A:set (real_line_metric R):=[set y:R | (y<=b^+2)%R].
have hA:measure_measurable mu A.
  apply:(@borel_regular_borel_measurable R (real_line_metric R) mu hm (lebesgue_scalar_borel_regular R)).
  apply:closed_borel_set.
  exact:(@order_closed_lower_ray_closed _ [the orderTopologicalType _ of R^o] (b^+2)%R).
have hFull:=@real_total_integral_scale R R mu hm (gamma_positive_completion s)
  (euler_gamma hs) (2%R:R) (euler_gamma_completed_integral hs).
have [a [c [ha [hc hSum]]]]:=
  (@measure_integral_measurable_split R R mu hm A
    (real_total_integrand (fun x=>(2*gamma_positive_completion s x)%R))
    (2*euler_gamma hs)%R%:E hA).1 hFull.
exists a; apply:(@measure_integral_graph_equivalent R R mu _ _ a _ ha).
apply:real_subset_total_graph.
- move=>x hx; by rewrite /gamma_square_target_cutoff hx.
- move=>x hx; have hNot:(x<=b^+2)%R=false by apply/negP.
  by rewrite /gamma_square_target_cutoff hNot.
Qed.

(** Source for [gamma_square_bounded_integral_transfer]: the actual
    scalar area formula transforms the bounded Gamma target
    integral to the bounded Gaussian source integral, Federer
    3.2.13, p. 250. *)
Lemma gamma_square_bounded_integral_transfer (R:realType) (s b:R) a:
  (0<b)%R ->
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (gamma_square_target_cutoff s b)) a ->
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (gamma_square_source_cutoff s b)) a.
Proof.
move=>hb hT.
have hOrder:((-b)%R<=b)%R by lra.
have hBound:=@real_metric_closed_interval_bounded R (-b)%R b hOrder.
have hA:measure_measurable (@lebesgue_scalar_measure R) `[(-b)%R,b].
  apply:(@borel_regular_borel_measurable R (real_line_metric R) _
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  apply:closed_borel_set; exact:segment_closed_real.
have hTarget:=measure_integral_graph_equivalent
  (fun y z=>iff_sym (gamma_square_area_target_graph s hb y z)) hT.
have hSource:=(federer_3_2_6_1_scalar (gamma_positive_completion s)
  (@scalar_square_locally_absolutely_continuous R) hBound hA a).2 hTarget.
exact:measure_integral_graph_equivalent (gamma_square_area_source_graph s hb) hSource.
Qed.
