(** Federer (1969), 2.6.4, p. 119, corrected final assertion: measurability
    of K(X times Y) for the product of representing measures. A countable
    sequence of uniform finite separated approximations supplies the proof
    without any countable base assumption. This supports erratum p. 2, book
    p. 119 line 19. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalLimits
  CompactSupportFunctionUP CompactProductSections CompactCutoffUP CompactCutoff CompactProductApproximationUP
  CompactProductApproximationSealed CompactSeparatedSumIntegrability SummableRealFunctionUP SummableRealNormed
  TotalScalarMeasurability ScalarCountableEmbedding ProductMeasure StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_function_measurable]: supporting
    product-measure measurability for the corrected representation
    assertion in Federer 2.6.4, p. 119, erratum p. 2.
    No global sigma-finiteness or countable topology base is assumed. *)
Theorem compact_product_function_measurable (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (h : (X*Y) -> R) :
  hausdorff_space X -> hausdorff_space Y -> locally_compact (@setT Y) ->
  (forall f, compactly_supported_continuous_functions f -> summable_real_functions alpha f) ->
  (forall g, compactly_supported_continuous_functions g -> summable_real_functions beta g) ->
  compactly_supported_continuous_functions h ->
  is_measure_measurable_function (product_measure ha hb) (real_total_integrand h).
Proof.
move=> hX hY hlY hAs hBs hh.
pose K := fst @` real_function_support h.
pose L := snd @` real_function_support h.
have hK : compact K := compact_product_first_projection hh.2.
have hL : compact L := compact_product_second_projection hh.2.
pose v := @compact_cutoff R Y L hY hlY hL.
have hv := @compact_cutoff_specification R Y L hY hlY hL.
have hz x y : ~(K x /\ L y) -> h (x,y)=0.
  move=> hn; apply: real_function_zero_off_support=> hs; apply: hn; split; by exists (x,y).
pose e n := (n.+1%:R : R)^-1.
have he n : 0<e n by rewrite /e invr_gt0 ltr0n.
have hex n := @CompactProductApproximation.exists_approximation R X Y h K L v (e n)
  hX hY hlY hh hK hz hv (he n).
pose q n := sval (cid (hex n)).
have hq n := svalP (cid (hex n)).
have hqi n : summable_real_functions (product_measure ha hb) (q n).
  exact (@finite_compact_separated_sum_summable R X Y alpha beta ha hb hAs hBs _ (hq n).1).
have hqm n : is_measure_measurable_function (product_measure ha hb)
    (partial_function_total (q n : (X*Y) -> real_line_metric R)).
  have [a hi] := hqi n.
  exact (@total_scalar_real_measurable R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) _
    (@real_integrand_measurable_scalar_norm R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) _ hi.1)).
have hcv p : (fun n => (q n p : real_line_metric R)) @ \oo --> (h p : real_line_metric R).
  apply/cvg_ballP=> d hd.
  have [N hN] := @uniform_mesh_small R 0 1 d ler01 hd.
  exists N=> // n hn; change (is_true (`|h p-q n p|<d)).
  apply: le_lt_trans ((hq n).2.2 p) _.
  have hh' := hN n hn; by rewrite subr0 mul1r in hh'.
have hm := @measurable_total_functions_almost_limit R (Choice.clone (X*Y)%type _)
  [the metricType R of real_line_metric R] _ (product_measure_is_measure ha hb) q h setT
  hqm (measure_almost_everywhere_true (product_measure_is_measure ha hb)) (fun p _ => hcv p).
exact (@scalar_real_integrand_measurable R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) h
  (@real_total_scalar_measurable R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) h hm)).
Qed.
