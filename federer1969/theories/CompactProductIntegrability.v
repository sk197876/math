(** Federer (1969), 2.6.4, p. 119, corrected final assertion: every member
    of K(X times Y) is summable for the product of representing measures.
    Uniform separated approximation gives measurability; a product of
    compact cutoffs gives a summable majorant. This supports erratum p. 2,
    book p. 119 line 19. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactProductSections CompactSupportUniformBound
  CompactCutoffUP CompactCutoff CompactProductMeasurability MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureAbsoluteSummability PartialExtendedOrderLoci PartialAbsolutePartsGraph
  PartialExtendedArithmetic SummableRealFunctionUP SummableRealArithmetic ProductMeasure SeparatedProductIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_function_summable]: supporting
    product-measure summability in Federer 2.6.4, p. 119,
    as corrected in erratum p. 2. No measurability of
    arbitrary compact subsets is needed: compact cutoffs supply the
    majorant directly. *)
Theorem compact_product_function_summable (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (h : (X*Y) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  (forall f, compactly_supported_continuous_functions f -> summable_real_functions alpha f) ->
  (forall g, compactly_supported_continuous_functions g -> summable_real_functions beta g) ->
  compactly_supported_continuous_functions h -> summable_real_functions (product_measure ha hb) h.
Proof.
move=> hX hlX hY hlY hAs hBs hh.
have hmeas := @compact_product_function_measurable R X Y alpha beta ha hb h hX hY hlY hAs hBs hh.
pose K := fst @` real_function_support h.
pose L := snd @` real_function_support h.
have hK : compact K := compact_product_first_projection hh.2.
have hL : compact L := compact_product_second_projection hh.2.
pose u := @compact_cutoff R X K hX hlX hK.
have hu := @compact_cutoff_specification R X K hX hlX hK.
pose v := @compact_cutoff R Y L hY hlY hL.
have hv := @compact_cutoff_specification R Y L hY hlY hL.
have [M [hM hbound]] := compact_support_uniform_bound hh.
pose H (p : X*Y) := M*(u p.1*v p.2).
have hHs : summable_real_functions (product_measure ha hb) H.
  apply: (@summable_real_scale R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb) _ M).
  exact (@separated_product_summable R X Y alpha beta ha hb u v
    (@hAs u (compact_cutoff_function hu)) (@hBs v (compact_cutoff_function hv))).
have hdom p : `|h p|<=H p.
  case: p=> x y; case: (pselect (K x /\ L y))=> [[hx hy]|hn].
  - rewrite /H /= /u /v (compact_cutoff_on_set hu hx) (compact_cutoff_on_set hv hy) !mulr1.
    exact: hbound.
  - have hz : h (x,y)=0.
      apply: real_function_zero_off_support=> hs; apply: hn; split; by exists (x,y).
    rewrite hz normr0 /H /=.
    exact (mulr_ge0 hM (mulr_ge0 (andP (compact_cutoff_range hu x)).1 (andP (compact_cutoff_range hv y)).1)).
refine (proj1 (@measure_dominated_summable R (Choice.clone (X*Y)%type _) _
  (product_measure_is_measure ha hb) (real_total_integrand h) (real_total_integrand H) hmeas hHs _)).
apply: (@measure_almost_everywhere_mono R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)
  setT _ _ (measure_almost_everywhere_true (product_measure_is_measure ha hb)))=> p _.
exists (`|h p|)%:E,(H p)%:E; split.
- exists (h p)%:E; split; first by apply/real_total_integrand_graph.
  by rewrite abse_EFin.
- split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hdom.
Qed.
