(** Federer (1969), 2.3.6, p. 77, final paragraph: reduce to a closed
    separable subset containing almost all values on A. Source context:
    MeasurableFiniteImageSupport.v. Values on the null exceptional set are
    removed from A before applying Lusin, so continuity of the original
    function holds everywhere on the final set, not merely almost
    everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialFunctionExtensionUP PartialContinuityUP PartialContinuityTotal
  PartialContinuityAgreement MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  MeasureFiniteClosure MeasurableFunctionUP MeasurableFunctionBorel MeasurableTotalBasic
  TopologicalBorel ClosedSubsetBorelRetractionUP ClosedSubsetBorelRetractionSealed LusinApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_closed_separable_range_transfer]: supporting
    transfer of Lusin's conclusion to the original partial function
    in Federer 2.3.6, p. 77, final paragraph. The supplied
    total extension is used only for the image measure and range reduction. *)
Theorem lusin_closed_separable_range_transfer (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu) (P : set (set X))
    (f : partial_function X Y) (g : X -> Y) (A : set X) (S : set Y)
    (s0 : metric_subset S) (D : set (metric_subset S)) (e : R) :
  has_lusin_approximation mu P -> is_measure_measurable_function mu f ->
  is_partial_function_total_extension f g ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_measurable mu A -> mu A < +oo -> closed S -> countable D -> dense D ->
  mu (A `&` (g @^-1` (~` S))) = 0 -> (0 < e)%R ->
  exists C, P C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
Proof.
move=> hL hf hfg hg hA hfin hS hc hd hnull he.
pose r := @ClosedSubsetBorelRetraction.value R Y S s0 hS.
have hr := @ClosedSubsetBorelRetraction.laws R Y S s0 hS.
pose h x := r (g x).
have hh : is_measure_measurable_function mu (partial_function_total h).
  exact (@measurable_total_borel_postcomposition R X Y (metric_subset S) mu hm g r hg hr.1).
pose B := (A `&` partial_function_domain f) `&` (g @^-1` S).
have hmB : measure_measurable mu B.
  apply: (@measure_measurable_intersection R X mu hm).
  - apply: (@measure_measurable_intersection R X mu hm _ _ hA).
    exact: (@conull_partial_function_domain_measurable R X Y mu hm f (measurable_function_domain hf)).
  - have hb := @measurable_function_borel_preimage R X Y mu hm (partial_function_total g) hg S (closed_borel_set hS).
    by rewrite partial_function_total_preimage in hb.
have hBA : B `<=` A by move=> x [[hx _] _].
have hfinB : mu B < +oo := le_lt_trans (@measure_mono R X mu hm B A hBA) hfin.
have hnullB : mu (A `\` B) = 0.
  have hcover : (A `\` B) `<=` (~` partial_function_domain f) `|` (A `&` (g @^-1` (~` S))).
    move=> x [ha hn]; case: (pselect (partial_function_domain f x))=> hx; last by left.
    right; split=> // hs; apply: hn; by split; first split.
  have hz := @measure_null_union R X mu hm _ _ (measurable_function_domain hf) hnull.
  exact: (@measure_null_subset R X mu hm _ _ hcover hz).
have [C [hC [hCB [herr hcont]]]] := hL (metric_subset S) D hc hd (partial_function_total h) hh B hmB hfinB e he.
exists C; split=> //; split.
- move=> x hx; exact: hBA x (hCB x hx).
- split.
  + have hcover : (A `\` C) `<=` (A `\` B) `|` (B `\` C).
      move=> x [ha hn]; case: (pselect (B x))=> hb; [right|left]; by split.
    have hb := @measure_binary_cover R X mu hm _ _ _ hcover.
    rewrite hnullB add0e in hb; exact: le_lt_trans hb herr.
  + have hcts := (proj1 (partial_continuity_total_iff C h)) hcont.
    have hvcts : {within C, continuous (fun x => (val (h x) : Y))}.
      move=> x; exact: continuous_comp (hcts x) (@metric_subset_inclusion_continuous R Y S (h x)).
    have hvc := (proj2 (partial_continuity_total_iff C (fun x => (val (h x) : Y)))) hvcts.
    apply: (@partial_continuity_agreement X Y C (partial_function_total (fun x => (val (h x) : Y))) f _ hvc).
    move=> x hx; have [[_ [y hy]] hs] := hCB x hx.
    exists y; split=> //; change (val (r (g x)) = y).
    rewrite (hr.2 (g x) hs); exact: hfg x y hy.
Qed.
