(** Federer (1969), 2.10.22, pp. 185–186:
    summability and positivity force small diameters
    in the limit tail, and continuity permits
    interior-containing compact replacements with arbitrarily
    small added total cost. Geometric errors make
    the printed simultaneous choices explicit. Source
    editions: CompactGeneratorCostUP.v; the underlying
    open-refinement argument is CompactOuterApproximation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactGeneratorCostUP CompactGeneratorCostLaws CompactOuterApproximation MaskedCompactGenerators
  NonnegativeSum NonnegativeSumAdd NonnegativeSeriesTails GeometricErrorBudget LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_masked_series_small_diameter]: supporting
    diam D_k tending to zero in 2.10.22,
    p. 185. Cost order is unnecessary for the
    limit series: a small sum tail bounds each
    active cost, and compactness supplies the diameter gap. *)
Theorem compact_masked_series_small_diameter (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (K : set (compact_hausdorff_space X)) (v : nat -> bool*compact_hausdorff_space X) :
  compact K -> (forall k, K (v k).2) ->
  (nonnegative_sum setT (fun k=>(masked_compact_cost c (v k))%:E)< +oo)%E ->
  forall e : R, 0<e -> exists N, forall k, (N<=k)%N -> (v k).1 -> compact_metric_diameter (v k).2<e.
Proof.
move=> hK hv hs e he.
have [eta [heta hgap]] := @compact_hyperspace_cost_gap R X c hc K e hK he.
have h0 k : (0<=(masked_compact_cost c (v k))%:E)%E.
  rewrite lee_fin /masked_compact_cost; case: (v k).1=> //; exact: compact_cost_nonnegative_law hc (v k).2.
have [N hN] := nonnegative_series_tail_small h0 hs heta.
exists N=> k hNk hk; apply: hgap (hv k) _.
have hh := @nonnegative_sum_term R [the choiceType of (nat : Type)] [set k | (N<=k)%N]
  (fun k=>(masked_compact_cost c (v k))%:E) k hNk.
have hb := le_lt_trans hh hN; by rewrite /masked_compact_cost hk lte_fin in hb.
Qed.

(** Source for [compact_masked_open_tail_refinement]: supporting
    simultaneous S_k choices in 2.10.22,
    p. 186. Every selected replacement remains
    a genuine compact generator. Inactive positions
    contribute zero; no cost monotonicity is assumed. *)
Theorem compact_masked_open_tail_refinement (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (v : nat -> bool*compact_hausdorff_space X) (J : set nat) (delta e : R) :
  metric_boundedly_compact X -> 0<e ->
  (forall k, J k -> (v k).1 -> compact_metric_diameter (v k).2<delta) ->
  exists w : nat -> bool*compact_hausdorff_space X,
    (forall k, J k -> masked_compact_set (v k) `<=` interior (masked_compact_set (w k))) /\
    (forall k, J k -> (w k).1 -> compact_metric_diameter (w k).2<delta) /\
    (nonnegative_sum J (fun k=>(masked_compact_cost c (w k))%:E)<=
      nonnegative_sum J (fun k=>(masked_compact_cost c (v k))%:E)+(e/2)%:E)%E.
Proof.
move=> hX he hd.
pose a k := geometric_error_budget e k.
have ha k : 0<a k := geometric_error_budget_positive k he.
have hex k : exists z : bool*compact_hausdorff_space X, J k ->
    masked_compact_set (v k) `<=` interior (masked_compact_set z) /\
    (z.1 -> compact_metric_diameter z.2<delta) /\
    masked_compact_cost c z<=masked_compact_cost c (v k)+a k.
  case: (pselect (J k))=> [hk|hk]; last by exists (v k)=> hk'; exact: (False_ind _ (hk hk')).
  case hvk: (v k).1.
  - have hdiam := hd k hk hvk.
    have hcsmall : c (v k).2<c (v k).2+a k by rewrite ltrDl.
    have [C [hVC [hCd hCc]]] := @compact_cost_open_refinement R X c hc (v k).2 delta (c (v k).2+a k) hX hdiam hcsmall.
    exists (true,C)=> _; rewrite /masked_compact_set /masked_compact_cost /= hvk.
    split=> //; split; [by move=> _|exact: ltW hCc].
  - exists (false,(v k).2)=> _; rewrite /masked_compact_set /masked_compact_cost /= hvk.
    split; first by move=> x [].
    split; [by move=> hfalse|rewrite add0r; exact: ltW (ha k)].
pose w k := projT1 (cid (hex k)).
have hw k : J k -> masked_compact_set (v k) `<=` interior (masked_compact_set (w k)) /\
    ((w k).1 -> compact_metric_diameter (w k).2<delta) /\
    masked_compact_cost c (w k)<=masked_compact_cost c (v k)+a k := projT2 (cid (hex k)).
exists w; split; first by move=> k hk; exact: (hw k hk).1.
split; first by move=> k hk; exact: (hw k hk).2.1.
have h0 k : (0<=(masked_compact_cost c (v k))%:E)%E.
  rewrite lee_fin /masked_compact_cost; case: (v k).1=> //; exact: compact_cost_nonnegative_law hc (v k).2.
have ha0 k : (0<=(a k)%:E)%E by rewrite lee_fin; exact: ltW (ha k).
have hh : (nonnegative_sum J (fun k=>(masked_compact_cost c (w k))%:E)<=
    nonnegative_sum J (fun k=>(masked_compact_cost c (v k))%:E+(a k)%:E)%E)%E.
  apply: nonnegative_sum_mono=> k hk; rewrite -EFinD lee_fin; exact: (hw k hk).2.2.
rewrite nonnegative_sum_add in hh; [|by move=> k _; exact: h0|by move=> k _; exact: ha0].
apply: le_trans hh _; apply: leeD; first exact: lexx _.
apply: le_trans (nonnegative_sum_subset (fun k=>(a k)%:E) (fun k _=>Logic.I)) _.
exact: geometric_error_sum_bound he.
Qed.
