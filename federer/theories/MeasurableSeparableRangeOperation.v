(** Federer (1969), 2.3.8, p. 78: essential separability permits measurable
    continuous binary operations. Source context: ClosedLinearSpanUP.v. We
    use the sealed Borel range retraction from 2.3.6 and the project's
    product measurability theorem from 2.3.2(5). Neither input is required
    to land in the subspace everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePairs
  MeasurablePostcomposition MeasurableAlmostModification BorelFunctionBasic
  MetricSubsetBackground MetricSubsetPairInclusion CountableOpenBaseUP
  SeparableMetricBaseSealed ClosedSubsetBorelRetractionUP ClosedSubsetBorelRetractionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_closed_separable_range_operation]: supporting
    precise reduction for additive closure in Federer 2.3.8, p. 78 Any
    continuous binary operation preserves measurability when both partial
    functions are essentially valued in one closed separable set. The common
    domain and null exceptions are retained. *)
Theorem measurable_closed_separable_range_operation (R : realType) (X : choiceType)
    (Y : metricType R) (W : topologicalType) (mu : set X -> \bar R)
    (hm : is_measure mu) (S : set Y) (s0 : metric_subset S)
    (D : set (metric_subset S)) (f g : partial_function X Y) (b : Y*Y -> W) :
  closed S -> countable D -> dense D -> continuous b ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  mu (partial_function_preimage f (~` S)) = 0 ->
  mu (partial_function_preimage g (~` S)) = 0 ->
  is_measure_measurable_function mu (partial_function_postcompose (partial_function_pair f g) b).
Proof.
move=> hS hc hd hb hf hg hfs hgs.
pose r := @ClosedSubsetBorelRetraction.value R Y S s0 hS.
have hr := @ClosedSubsetBorelRetraction.laws R Y S s0 hS.
pose F := partial_function_postcompose f r.
pose G := partial_function_postcompose g r.
have hF : is_measure_measurable_function mu F :=
  @measurable_function_borel_postcomposition R X Y (metric_subset S) mu hm f r hf hr.1.
have hG : is_measure_measurable_function mu G :=
  @measurable_function_borel_postcomposition R X Y (metric_subset S) mu hm g r hg hr.1.
pose U := @SeparableMetricBase.value R (metric_subset S) D hc hd.
have hU := @SeparableMetricBase.laws R (metric_subset S) D hc hd.
have hpair := @measurable_partial_function_pair R X (metric_subset S) (metric_subset S)
  nat nat mu hm F G U U (countable_base_open hU) (countable_base_refines hU)
  (countable_base_open hU) (countable_base_refines hU) hF hG.
pose H := partial_function_postcompose (partial_function_pair F G)
  (fun p => b (val p.1,val p.2)).
have hH : is_measure_measurable_function mu H.
  apply: (@measurable_function_borel_postcomposition R X _ W mu hm _ _ hpair).
  apply: continuous_borel_function; exact: continuous_binary_operation_on_subsets hb.
pose E := partial_function_preimage f (~` S) `|` partial_function_preimage g (~` S).
have hE : mu E = 0 := @measure_null_union R X mu hm _ _ hfs hgs.
have hdom := @measure_almost_everywhere_and R X mu hm _ _
  (measurable_function_domain hf) (measurable_function_domain hg).
have hec : measure_almost_everywhere mu (~` E) by rewrite /measure_almost_everywhere setCK.
have hP := @measure_almost_everywhere_and R X mu hm _ _ hdom hec.
apply: (@measurable_function_almost_equal R X W mu hm H _ hH).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hP).
move=> x [[[a ha] [z hz]] hbad].
have hSa : S a.
  apply: contrapT=> hn; apply: hbad; left; exists a; by split.
have hSz : S z.
  apply: contrapT=> hn; apply: hbad; right; exists z; by split.
exists (b (a,z)); split.
- exists (r a,r z); split.
  + split; [exists a|exists z]; by split.
  + by rewrite /= (hr.2 a hSa) (hr.2 z hSz).
- exists (a,z); split; first by split.
  by [].
Qed.
