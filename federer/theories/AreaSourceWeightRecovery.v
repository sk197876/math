(** Federer (1969), 3.2.5(3), p. 245: on
    a measurable subset of the actual positive-Jacobian
    locus, recover g composed with f by dividing the
    measurable weighted integrand by its positive Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealReciprocalBorel
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionPair PartialZeroExtension
  PartialDensityProduct MeasureUP MeasurableFunctionUP MeasurablePostcomposition MeasurableRealArithmetic
  MeasurableZeroExtension MeasurableGraphEquivalence LipschitzUP Jacobian EuclideanJacobianMeasurable
  BorelAreaSelection AreaTransformIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [area_source_positive_subset_pullback_measurable]:
    the implication from measurability of the left integrand
    to measurability of beta times (g composed with f)
    in Federer 3.2.5(3), p. 245. Division is used
    only where the original Jacobian is defined and positive. *)
Theorem area_source_positive_subset_pullback_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A B
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) ->
  measure_measurable (@euclidean_lebesgue_measure R m) B ->
  B `<=` A `&` positive_euclidean_jacobian_locus f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (partial_function_zero_extension (0:real_line_metric R) B (partial_function_total (fun x=>g (f x)))).
Proof.
move=>hLip hSource hB hBAP.
pose mu:=@euclidean_lebesgue_measure R m.
have hm:=euclidean_lebesgue_is_measure R m.
pose v:=partial_function_postcompose (area_transform_source_integrand f A g)
  (fun z:extended_real_line R=>(fine z:real_line_metric R)).
pose w:=partial_function_postcompose (euclidean_jacobian m setT f)
  (fun r:real_line_metric R=>(r^-1:real_line_metric R)).
pose u:=partial_real_function_multiply v w.
have hv:=measurable_function_borel_postcomposition hm hSource (@extended_finite_projection_borel R).
have hw:=measurable_function_borel_postcomposition hm (euclidean_top_jacobian_measurable hLip)
  (@real_reciprocal_borel R).
have hu:=measurable_real_function_multiply hm hv hw.
have hValue x:B x -> partial_function_graph u x (g (f x)).
  move=>hx; have [hAx [r [hr hrPos]]]:=hBAP x hx.
  have hJac:partial_function_graph (extended_euclidean_jacobian f) x r%:E.
    exists r; by split.
  have hWeighted:partial_function_graph (area_transform_source_integrand f A g) x (g (f x)*r)%:E.
    apply:(partial_function_zero_extension_on _ _ _ hAx).2.
    apply/partial_density_product_graph; exists (g (f x))%:E,r%:E; split=>//; split=>//.
  have hV:partial_function_graph v x (g (f x)*r).
    exists (g (f x)*r)%:E; by split.
  have hW:partial_function_graph w x r^-1 by exists r; split.
  exists ((g (f x)*r),r^-1); split; first by split.
  have hr0:r!=0%R by rewrite (gt_eqF hrPos).
  by rewrite /= -mulrA (mulfV hr0) mulr1.
have hCut:=@measurable_zero_extension R [the choiceType of (R_n R m:Type)]
  [the topologicalType of real_line_metric R] mu hm 0 B u hB hu.
apply:(@measurable_function_graph_equivalent R _ [the topologicalType of real_line_metric R] mu _ _ _ hCut).
move=>x z; case:(pselect (B x))=>hx.
- rewrite !(partial_function_zero_extension_on _ _ _ hx); split.
  + move=>hz; exact (partial_function_single_valued (hValue x hx) hz).
  + move=>hz; change (g (f x)=z) in hz; rewrite -hz; exact (hValue x hx).
- by rewrite !(partial_function_zero_extension_off _ _ _ hx).
Qed.
