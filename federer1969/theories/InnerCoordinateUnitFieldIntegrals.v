(** Federer (1969), 3.2.27, p. 263: the
    vector of absolute orthonormal coordinates of the
    unit tangent field has integral coordinates a_lambda.
    State the original field and integral laws independently;
    all auxiliary selected maps remain local to existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  HilbertFormCompactness OrthonormalFamilies OrthonormalParseval OrthonormalCoordinateModulus
  InnerNonnegativeUnitIntegralBounds LinearBasis RealNormUP NormMetric NormMetricScaleContinuity ContinuousRealFunctional
  PartialFunctionUP PartialFunctionPostcomposition ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  BorelFunctionBasic MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_unit_field_coordinate_integrals]: the
    definition of Xi and both integral inequalities in
    3.2.27, p. 263. Absolute-coordinate replacement
    preserves norm and is continuous. Finite-source L1
    integration and continuous dual evaluations prove
    existence of the actual finite coordinate masses.
    No derivative or projection profile is postulated. *)
Theorem inner_unit_field_coordinate_integrals (R:realType) (X:choiceType)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    (I:finType) (e:I->V) (mu:set X->\bar R)
    (T:partial_function X (inner_metric_space hB)):
  orthonormal_family B e ->is_basis e ->is_measure mu ->mu setT < +oo ->
  is_measure_measurable_function mu T ->
  (forall x v,partial_function_graph T x v ->inner_norm hB v= 1%R) ->
  exists a:I->R,
    (forall i,is_measure_integral mu
      (partial_function_postcompose T (fun v=>(`|B v (e i)|)%:E:extended_real_line R)) (a i)%:E) /\
    (Num.sqrt (\sum_i (a i)^+2))%:E<=mu setT /\
    mu setT<=(\sum_i a i)%R%:E.
Proof.
move=>he hBasis hMu hFinite hT hUnit.
have [A hA]:=@orthonormal_coordinate_modulus_exists R V B hB I e he.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
have hContinuous:continuous (A:inner_metric_space hB->real_norm_metric_space hN).
  apply:(@metric_fixed_lipschitz_continuous R (inner_metric_space hB) (real_norm_metric_space hN)
    A 1%R ler01)=>x y.
  rewrite inner_metric_distanceE real_norm_metric_distanceE mul1r.
  exact:(@orthonormal_coordinate_modulus_nonexpanding R V B hB I e A he hBasis hA x y).
pose f:=partial_function_postcompose T (fun v=>(A v:real_norm_metric_space hN)).
have hF:is_measure_measurable_function mu f.
  exact:(@measurable_function_borel_postcomposition R X
    [the topologicalType of inner_metric_space hB]
    [the topologicalType of real_norm_metric_space hN] mu hMu T A hT
    (continuous_borel_function hContinuous)).
have hFUnit x v:partial_function_graph f x v ->inner_norm hB v= 1%R.
  move=>[u [hu <-]].
  rewrite (@orthonormal_coordinate_modulus_norm R V B hB I e A he hBasis hA).
  exact:hUnit x u hu.
have hFPositive x v i:partial_function_graph f x v ->(0<=B v (e i))%R.
  move=>[u [hu <-]]; rewrite hA; exact:normr_ge0.
have [y [hY [hLower hUpper]]]:=@finite_inner_nonnegative_unit_integral_bounds R X V B hB I e mu f
  he hBasis hMu hFinite hF hFUnit hFPositive.
pose a i:R:=B y (e i).
have hCoordinate i:is_measure_integral mu
    (partial_function_postcompose T (fun v=>(`|B v (e i)|)%:E:extended_real_line R)) (a i)%:E.
  pose alpha:=inner_coordinate hB (e i).
  have hAlpha:is_continuous_real_functional hN alpha.
    apply:(@bounded_real_functional_continuous R V N hN alpha (inner_norm hB (e i))
      (inner_norm_nonnegative hB _))=>v.
    rewrite /alpha inner_coordinateE mulrC; exact:inner_cauchy.
  have hIntegral:=hY.2 alpha hAlpha.
  have hEvalValue:alpha y=a i by rewrite /alpha inner_coordinateE.
  rewrite hEvalValue in hIntegral.
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hIntegral)=>x z.
  split.
  - move=>[v [[u [hu hAu]] hAlphaZ]].
    exists u; split; first exact hu.
    change ((alpha v)%:E=z) in hAlphaZ.
    by rewrite /alpha inner_coordinateE -hAu hA in hAlphaZ.
  - move=>[u [hu hValue]].
    exists (A u); split; first by exists u.
    change ((alpha (A u))%:E=z); by rewrite /alpha inner_coordinateE hA.
have hNorm:(inner_norm hB y)=Num.sqrt (\sum_i (a i)^+2).
  rewrite /a -(@orthonormal_parseval R V B hB I e he hBasis y) -inner_norm_sqr
    sqrtr_sqr (ger0_norm (inner_norm_nonnegative hB y)); reflexivity.
exists a; split; first exact hCoordinate; split; last exact hUpper.
by rewrite -hNorm.
Qed.
