(** Federer (1969), 4.1.1, p. 346: pair a
    measurable compactly supported vector function
    with a weak dual field whose norm is
    integrable on that compact set. This supporting
    theorem keeps the dual abstract and uses
    the original real integral and 2.5.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground RealFunctionalNormUP ContinuousDualUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP VectorDaniellHypotheses VectorDaniellRationalSpan
  MeasurableVariableDualPairing MeasurableTotalCutoff RealTotalMeasurabilityProjection
  MeasureFiniteRealScaleIntegral VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CompactDualPairing.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hSep:is_separable_normed_space hNY.
Variable xi:X->D.
Hypothesis hXi:forall y:Y,is_measure_measurable_function mu
  (partial_function_total (fun x=>(ed (xi x) y:real_line_metric R))).

(** Source for [integrable_compact_dual_pairing]: the
    original integral of the pairing is finite
    and bounded by the vector supremum times
    the local dual-norm integral, supporting
    Federer 4.1.1, p. 346. The field
    need not have bounded norm. *)
Theorem integrable_compact_dual_pairing (S:set X) (eta:X->Y) (B b:R):
  measure_measurable mu S ->
  is_measure_measurable_function mu
    (partial_function_total (eta:X->real_norm_metric_space hNY)) ->
  (forall x,~S x ->eta x=0) ->0<=B ->(forall x,S x ->NY (eta x)<=B) ->
  is_measure_integral mu (real_total_integrand
    (fun x=>if pselect (S x) then DN (xi x) else 0)) b%:E ->
  exists c:R,is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (eta x))) c%:E /\
    `|c|<=B*b.
Proof.
move=>hS hEta hZero hB hEtaBound hLocal.
pose G x:=if pselect (S x) then DN (xi x) else 0.
pose k x:Hom Y R^o:=if pselect (S x) then ed (xi x) else 0.
have hG x:0<=G x.
  rewrite /G; case:pselect=>// hx; exact:real_functional_norm_nonnegative (continuous_dual_norm_laws hD (xi x)).
have hk x y:`|k x y|<=G x*NY y.
  rewrite /k /G; case:pselect=>hx.
  - exact:(real_functional_norm_bound (continuous_dual_norm_laws hD (xi x)) y).
  - by rewrite hom_zeroE normr0 mul0r.
have hGm:=real_total_measurability_projection hm hLocal.1.
have [F hF]:=rational_dense_subspace_exists hSep.
have hComp y (_:F y):is_measure_measurable_function mu
    (partial_function_total (fun x=>(k x y:real_line_metric R))).
  have hCut:=@measurable_total_cutoff R X [the topologicalType of real_line_metric R]
    mu hm S (fun x=>(ed (xi x) y:real_line_metric R)) 0 hS (hXi y).
  have hEq:(fun x=>(k x y:real_line_metric R))=
    (fun x=>if pselect (S x) then (ed (xi x) y:real_line_metric R) else 0).
    apply:funext=>x; rewrite /k; by case:pselect=>hx; rewrite ?hom_zeroE.
  by rewrite hEq.
have hPair:=@measurable_variable_dual_pairing R X Y NY hNY F hF mu hm k G hG hk hGm eta hComp hEta.
have hEq:(fun x=>k x (eta x))=(fun x=>ed (xi x) (eta x)).
  apply:funext=>x; rewrite /k; case:pselect=>hx; first reflexivity.
  by rewrite (hZero x hx) hom_zeroE linear0.
rewrite hEq in hPair.
have hBound x:`|ed (xi x) (eta x)|<=B*G x.
  have hEtaB:NY (eta x)<=B.
    case:(pselect (S x))=>hx; first exact:hEtaBound x hx.
    by rewrite (hZero x hx) (real_seminorm_zero hNY.1).
  have hStart:=hk x (eta x).
  have hEqx:=congr1 (fun f:X->R=>f x) hEq.
  rewrite hEqx in hStart.
  have hEnd:=ler_wpM2l (hG x) hEtaB.
  by rewrite mulrC; exact:le_trans hStart hEnd.
have hScale:=@measure_finite_real_total_scale_integral R X mu hm
  (fun x=>(G x:real_line_metric R)) b B hLocal.
exact:(real_total_dominated_integral hm hPair hScale hBound).
Qed.
End CompactDualPairing.
