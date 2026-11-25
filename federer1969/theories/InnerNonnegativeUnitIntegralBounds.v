(** Federer (1969), 3.2.27, p. 263: integrate the
    nonnegative orthonormal-coordinate field Xi. The vector
    integral norm gives one bound; the sum of its scalar
    coordinates gives the other. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  HilbertFormCompactness OrthonormalFamilies OrthonormalCoordinateModulus LinearBasis
  RealNormUP NormMetric ContinuousRealFunctional PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition ExtendedRealOrderTopology
  FiniteInnerUnitFieldIntegral MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralComparison FiniteMeasureBoundedNorm
  MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_coordinate_sum_dual_exists]: the
    sum of coordinates in the final bound of 3.2.27,
    p. 263, is evaluation by a continuous real dual
    vector. Cauchy's inequality proves continuity directly,
    without an external finite-dimensional duality theorem. *)
Lemma inner_coordinate_sum_dual_exists (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V):
  exists a:{linear V->R^o},
    is_continuous_real_functional (inner_norm_real_norm hB) a /\
    forall x,a x=(\sum_i B x (e i))%R.
Proof.
pose a:=inner_coordinate hB (\sum_i e i).
exists a; split.
- apply:(@bounded_real_functional_continuous R V (inner_norm hB) (inner_norm_real_norm hB)
    a (inner_norm hB (\sum_i e i)) (inner_norm_nonnegative hB _))=>x.
  rewrite /a inner_coordinateE mulrC; exact:inner_cauchy.
- move=>x; rewrite /a inner_coordinateE (inner_symmetric hB) -inner_coordinateE linear_sum.
  apply:eq_bigr=>i _; by rewrite inner_coordinateE (inner_symmetric hB).
Qed.

(** Source for [finite_inner_nonnegative_unit_integral_bounds]:
    the two integral inequalities in 3.2.27, p. 263.
    Unit norm gives the actual source mass; the positive
    coordinate sum dominates that norm at every defined
    point. Partial domains remain conull without any
    artificial outside value. *)
Theorem finite_inner_nonnegative_unit_integral_bounds (R:realType) (X:choiceType)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    (I:finType) (e:I->V) (mu:set X->\bar R)
    (f:partial_function X (real_norm_metric_space (inner_norm_real_norm hB))):
  orthonormal_family B e ->is_basis e ->is_measure mu ->mu setT < +oo ->
  is_measure_measurable_function mu f ->
  (forall x v,partial_function_graph f x v ->inner_norm hB v= 1%R) ->
  (forall x v i,partial_function_graph f x v ->(0<=B v (e i))%R) ->
  exists y:V,is_measure_vector_integral mu f y /\
    (inner_norm hB y)%:E<=mu setT /\
    mu setT<=(\sum_i B y (e i))%R%:E.
Proof.
move=>he hBasis hMu hFinite hF hUnit hPositive.
have [y [hY [hLower hNorm]]]:=@finite_inner_unit_field_vector_integral R X V B hB I e mu f
  hBasis hMu hFinite hF hUnit.
have [a [hA hEval]]:=@inner_coordinate_sum_dual_exists R V B hB I e.
have hScalar:=hY.2 a hA.
have hFin:mu setT \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hMu setT)).
pose b:R:=fine (mu setT).
have hMass:mu setT=b%:E by rewrite /b fineK.
have hConstant:=@finite_measure_constant_integral R X mu hMu b 1%R hMass.
rewrite mul1r -hMass in hConstant.
have hUpper:mu setT<=(a y)%:E.
  apply:(@measure_integral_monotone R X mu hMu _ _ _ _ hConstant hScalar).
  apply:(measure_almost_everywhere_mono hMu _ (measurable_function_domain hF))=>x [v hv].
  exists 1,(a v)%:E; split; first reflexivity; split.
  - exists v; by split.
  - rewrite lee_fin hEval.
    have hBound:=@orthonormal_nonnegative_norm_sum R V B hB I e v he hBasis (fun i=>hPositive x v i hv).
    by rewrite (hUnit x v hv) in hBound.
exists y; split; first exact hY; split; first exact hLower.
by rewrite hEval in hUpper.
Qed.
