(** Federer (1969), 4.1.5, p. 350:
    simultaneous recovery of a unit weak-dual
    density from its original ball integrals,
    for a finite localized measure. The null
    ball locus supplies every positive denominator;
    zero measures require no special nonzero premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses WeakDualScalarEvaluation
  PartialFunctionUP MeasurableFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext CenteredBallRelations CoveringFamilyLaws MetricClosedBalls
  TopologicalBorel BorelRegularMeasureUP SummableRealFunctionUP LocalAbsoluteIntegrability
  FiniteBoundedRealDifferentiation FiniteWeakDualDifferentiation NullBallLocus
  BallIntegralQuotientLimitUP CoveringBallIntegralQuotientLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_weak_dual_simultaneous_ball_quotients]:
    the literal ball quotient formula with one
    common conull set for every y, Federer
    4.1.5, p. 350. No separability of
    the whole dual is required. *)
Theorem finite_weak_dual_simultaneous_ball_quotients (R:realType) (X:metricType R)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (hSep:is_separable_normed_space hNY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (xi:X->D):
  is_measure_derivation_context mu (@centered_closed_ball_relation R X) ->
  (mu setT< +oo)%E ->
  is_measure_measurable_function mu
    (PartialFunctionBasic.partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) ->
  (forall x,DN (xi x)<= 1) ->
  measure_almost_everywhere mu [set x|forall y:Y,
    is_ball_integral_quotient_limit mu (real_total_integrand (fun z=>ed (xi z) y)) x (ed (xi x) y)].
Proof.
move=>hContext hFinite hXi hUnit.
have hClass:=derivation_context_measure hContext.
have hm:=derivation_measure_law hClass.
have hMeasurable:=@weak_dual_scalar_evaluation_measurable R X Y D ed xi O hO mu hm hXi.
have hBound:=@unit_dual_scalar_evaluation_bound R X Y NY hNY D ed DN hD xi hUnit.
have hMeans:=@finite_weak_dual_simultaneous_differentiation R X Y NY hNY hSep D ed DN hD O hO
  mu (@centered_closed_ball_relation R X) xi hContext hFinite hXi hUnit.
have hNonNull:measure_almost_everywhere mu (~` measure_null_ball_points mu).
  by rewrite /measure_almost_everywhere setCK; exact:measure_null_ball_points_null hContext.
have hGood:=measure_almost_everywhere_and hm hMeans hNonNull.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hGood)=>x [hAt hPositive] y.
apply:(@covering_ball_integral_quotient_limit R X mu
  (real_total_integrand (fun z=>ed (xi z) y)) x (ed (xi x) y) _ _ (hAt y)).
- move=>r hR.
  have hMassPositive:=outside_null_ball_points_positive hm hPositive hR.
  have hMassFinite:mu (metric_closed_ball x r) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm _)).
    exact:le_lt_trans (measure_mono hm (subsetT _)) hFinite.
  exists (fine (mu (metric_closed_ball x r))); split; first by rewrite fineK.
  by move:hMassPositive; rewrite -(fineK hMassFinite) lte_fin.
- move=>r hR.
  have hBallMeasurable:=@borel_regular_borel_measurable R X mu hm (derivation_measure_borel_regular hClass)
    (metric_closed_ball x r) (@TopologicalBorel.closed_borel_set X (metric_closed_ball x r) (@metric_closed_ball_closed R X x r)).
  have hBallBounded:=@covering_closed_ball_bounded R X x r (ltW hR).
  have hLocal:=@finite_bounded_real_locally_absolutely_integrable R X mu hm
    (fun z=>ed (xi z) y) (NY y) hFinite (hMeasurable y) (fun z=>hBound z y).
  have[a [b [_ [_ hIntegral]]]]:=@locally_absolutely_integrable_part_values R X mu
    (real_total_integrand (fun z=>ed (xi z) y)) hm (hMeasurable y) hLocal
    (metric_closed_ball x r) hBallBounded hBallMeasurable.
  by exists (a-b).
Qed.
