(** Federer (1969), 3.2.22, p. 260:
    compare the target area-transformed fibre mass with
    its ordinary coarea parameter mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP RectifiableCompactChartsUP RectifiableCompactChartLaws
  RectifiableChartPairPieces RectifiableChartPairFibreBounds MappingMultiplicity HausdorffMeasure MeasureUP
  EuclideanLinearJacobian LinearJacobianSandwich ExtendedFibreProductBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_target_fibre_product_bounds]:
    the second local integral comparison in Federer
    3.2.22, p. 260, before integration.
    Source fibre distortion contributes lambda^(m-mu),
    and target area distortion contributes lambda^mu.
    Their product is lambda^m. Actual chart differentials
    exist at every target parameter, so these bounds
    hold on all C, including zero and infinite fibres. *)
Theorem rectifiable_target_fibre_product_bounds (R:realType) m n mu v
    (lambda:R) (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R v)
    (gamma:R_n R mu->R_n R v) (G:R_n R v->R_n R mu) (Jg:R_n R mu->R):
  (mu<=m)%N ->(0<lambda)%R ->
  is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->
  (forall y,C y ->G (gamma y)=y) ->
  (forall y D,has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R v)) setT gamma y D ->Jg y=euclidean_linear_jacobian mu D) ->
  forall y,C y ->
  let P:=rectifiable_chart_pair_piece K C psi F gamma in
  let A:=rectifiable_chart_pair_parameters K C psi F gamma in
  let b:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
    (mapping_fibre F P (gamma y)) in
  let c:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-mu)
    (mapping_fibre (fun a=>G (F (psi a))) A y) in
  b*(Jg y)%:E<=(lambda^+m)%R%:E*c /\ c<=(lambda^+m)%R%:E*(b*(Jg y)%:E).
Proof.
move=>hDim hPositive hSource hTarget hInverse hJg y hy P A b c.
have hFibres:=@rectifiable_chart_pair_fibre_mass_bounds R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R mu))
  (inner_metric_space (@euclidean_inner_productP R v)) K C psi F gamma G lambda (0%R:R_n R m) (m-mu) y
  (uniform_compact_chart_bilipschitz hSource) hInverse hy.
have [D [hD hBounds]]:=rectifiable_chart_differential_bounds hTarget hy.
have hInv:(0<=lambda^-1)%R by rewrite invr_ge0; exact:ltW hPositive.
have hJac:=euclidean_top_jacobian_sandwich hInv (ltW hPositive)
  (fun x=>(hBounds x).1) (fun x=>(hBounds x).2).
rewrite exprVn -(hJg y D hD) in hJac.
have hNonnegative:(0<=Jg y)%R by rewrite (hJg y D hD); exact:euclidean_linear_jacobian_nonnegative.
have hb:0<=b:=@measure_nonnegative R (inner_metric_space (@euclidean_inner_productP R n))
  _ (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) _.
have hc:0<=c:=@measure_nonnegative R (inner_metric_space (@euclidean_inner_productP R m))
  _ (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-mu)) _.
have hResult:=extended_fibre_product_bounds (exprn_gt0 (m-mu) hPositive)
  (exprn_gt0 mu hPositive) hNonnegative hb hc hJac.1 hJac.2 hFibres.1 hFibres.2.
by rewrite -exprD (subnK hDim) in hResult.
Qed.
