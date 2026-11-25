(** Federer (1969), 3.2.5(3), p. 245, as used
    in 3.2.46, p. 282: recover the original real
    weight from its measurable product with a positive
    finite partial Jacobian on the selected subset. No
    original weight measurability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  ExtendedFiniteProjectionBorel RealReciprocalBorel PartialFunctionUP
  PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionPair
  PartialZeroExtension PartialDensityProduct MeasureStepIntegralIdentification
  MeasureUP MeasureRestriction MeasurableFunctionUP MeasurablePostcomposition
  MeasurableRealArithmetic MeasureRestrictedGraphAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_partial_density_weight_recovery]:
    the positive-Jacobian division in Federer 3.2.5(3),
    p. 245, supporting 3.2.46, p. 282. The
    actual finite Jacobian retains its partial domain; the
    original real weight is recovered only on W where
    positivity is proved, without a global weight premise. *)
Theorem positive_partial_density_weight_recovery (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (j : partial_function X (real_line_metric R))
    (S W : set X) (u : X -> real_line_metric R) :
  is_measure mu -> is_measure_measurable_function mu j ->
  W `<=` S -> (forall x, W x -> exists r, partial_function_graph j x r /\ 0<r) ->
  is_measure_measurable_function mu
    (partial_function_zero_extension (0%E : extended_real_line R) S
      (partial_density_product (partial_function_total (fun x=>((u x)%:E : extended_real_line R)))
        (partial_real_function_embed j))) ->
  is_measure_measurable_function (measure_restrict mu W) (partial_function_total u).
Proof.
move=> hMu hJ hWS hPositive hProduct.
pose F := partial_function_zero_extension (0%E : extended_real_line R) S
  (partial_density_product (partial_function_total (fun x=>((u x)%:E : extended_real_line R)))
    (partial_real_function_embed j)).
pose p := partial_function_postcompose F (fun z : extended_real_line R=>(fine z : real_line_metric R)).
pose q := partial_function_postcompose j (fun r : real_line_metric R=>r^-1).
pose v := partial_real_function_multiply p q.
have hP := @measurable_function_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hMu F (fun z=>(fine z : real_line_metric R))
  hProduct (@extended_finite_projection_borel R).
have hQ := @measurable_function_borel_postcomposition R X [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] mu hMu j (fun r=>r^-1) hJ (@real_reciprocal_borel R).
have hV := measurable_real_function_multiply hMu hP hQ.
apply: (@restricted_graph_agreement_measurable R X [the topologicalType of real_line_metric R]
  mu W v (partial_function_total u) hMu hV).
move=> x hx z.
have [r [hr hR]] := hPositive x hx.
have hR0 := lt0r_neq0 hR.
have hFValue : partial_function_graph F x (u x*r)%:E.
  apply/partial_function_zero_extension_graph; left; split; first exact: hWS x hx.
  apply/partial_density_product_graph; exists (u x)%:E,r%:E; split; first by [].
  split; first by exists r; split.
  by rewrite -EFinM.
have hPValue : partial_function_graph p x (u x*r).
  exists (u x*r)%:E; by split.
have hQValue : partial_function_graph q x r^-1 by exists r; split.
have hVValue : partial_function_graph v x (u x).
  exists (u x*r,r^-1); split; first by split.
  by rewrite /= mulfK.
split.
- move=> hz; exact: partial_function_single_valued hVValue hz.
- move=> hz; change (u x=z) in hz; by rewrite -hz.
Qed.
