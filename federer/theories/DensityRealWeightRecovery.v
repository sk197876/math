(** Federer (1969), 3.2.6, pp. 245–246: recover
    a real weight from its measurable product with a finite
    density. The reciprocal is used only on the positive
    finite-density locus, which is conull for the density measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealReciprocalBorel
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialDensityProduct
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasureDensityUP MeasureDensityCover MeasureDensityTransfer MeasurableFunctionUP MeasurablePostcomposition
  MeasurableRealArithmetic MeasurableAlmostModification FiniteDensityPositiveLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_density_real_weight_recovery]: supporting
    reverse measurability implication in the arbitrary-weight
    formula of Federer 3.2.6, p. 245. No global
    measurability of the original real weight is assumed. *)
Theorem finite_density_real_weight_recovery (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:partial_function X (extended_real_line R)) (g:X->real_line_metric R):
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu [set x|exists r:R,(0<=r)%R /\ partial_function_graph h x r%:E] ->
  is_measure_measurable_function mu
    (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h) ->
  is_measure_measurable_function nu (partial_function_total g).
Proof.
move=>hNu hh hFinite hProduct.
have hp:measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hFinite)=>x [r [hr hRx]].
  exists r%:E; split=>//; by rewrite lee_fin.
have hn:=@measure_density_is_measure R X mu nu hm h hNu hp.
pose u:=partial_function_postcompose
  (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h)
  (fun z:extended_real_line R=>(fine z:real_line_metric R)).
pose v:=partial_function_postcompose h (fun z:extended_real_line R=>(fine z:real_line_metric R)).
pose w:=partial_function_postcompose v (fun r:real_line_metric R=>(r^-1)%R).
pose q:=partial_real_function_multiply u w.
have hu:=measurable_function_borel_postcomposition hm hProduct (@extended_finite_projection_borel R).
have hv:=measurable_function_borel_postcomposition hm hh (@extended_finite_projection_borel R).
have hw:=measurable_function_borel_postcomposition hm hv (@real_reciprocal_borel R).
have hq:=measurable_real_function_multiply hm hu hw.
have hqn:=@measure_density_measurable_function R X [the topologicalType of real_line_metric R]
  mu nu hm h q hNu hp hq.
apply:(@measurable_function_almost_equal R X [the topologicalType of real_line_metric R]
  nu hn q (partial_function_total g) hqn).
apply:(@measure_almost_everywhere_mono R X nu hn _ _ _
  (finite_density_positive_almost hm hNu hFinite))=>x [r [hr hRx]].
exists (g x); split=>//.
have hr0:r!=0%R by rewrite (gt_eqF hr).
have hProd:partial_function_graph
    (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h) x (g x*r)%:E.
  apply/partial_density_product_graph; exists (g x)%:E,r%:E; split=>//; split=>//.
have huVal:partial_function_graph u x (g x*r)%R.
  exists (g x*r)%:E; by split.
have hvVal:partial_function_graph v x r by exists r%:E; split.
have hwVal:partial_function_graph w x (r^-1)%R by exists r; split.
exists ((g x*r)%R,(r^-1)%R); split; first by split.
by rewrite /= -mulrA (mulfV hr0) mulr1.
Qed.
