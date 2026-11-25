(** Federer (1969), 2.10.22, pp. 184–186: the bounded-target part of
    continuity below. The compact-cover array is extracted in F_(a,r+delta),
    using the Hausdorff compactness proved in 2.10.21. Zero-cost source
    generators are removed through actual nullity, before positive-cost
    ordering. No measurability of A_j is introduced. Source context and
    proof-route details: CompactGeneratorCostUP.v, CompactCostCoverRow.v,
    CompactArrayCluster.v and CompactCostLimitCoverBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactBallProfiles CompactHausdorffBall CompactGeneratorCostUP CompactCostSourceArray CompactCostArray
  CompactCostLimitArray CompactCostOpenResidual CompactCostLimitCoverBound MaskedCompactGenerators
  MetricClosedBalls MetricScaleEnvelopeUP MetricScaleCutoffCost CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryBorelRegular CaratheodoryMeasure BorelRegularMeasureUP
  TopologicalBorel MeasureUP MeasureBasic MeasureSplit NonnegativeSum SummableCostEnumerationUP
  RealMetricBackground LipschitzFunctionCompact ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_bounded_continuity_bound]: supporting
    bounded-target reduction of 2.10.22, pp. 184–186.
    Any common finite upper bound s on the row
    masses bounds the union mass. The cutoff remains
    finite and strictly positive, as in the book. *)
Theorem compact_cost_bounded_continuity_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta : R) (nu : set X -> \bar R) (A : nat -> set X) (a : X) (r s : R) :
  metric_boundedly_compact X -> 0<delta -> 0<=r -> 0<=s ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  (forall i j, (i<=j)%N -> A i `<=` A j) ->
  (forall j, A j `<=` metric_closed_ball a r) ->
  (forall j, (nu (A j)<=s%:E)%E) -> (nu (\bigcup_j A j)<=s%:E)%E.
Proof.
move=> hX hd hr hs hn hinc hA hbound.
pose mu := caratheodory_measure (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E).
have hmu := @caratheodory_measure_specification R X (compact_metric_set X) (fun C=>val C) (fun C=>(c C)%:E).
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := caratheodory_limit_is_measure hmu hc0.
have hnu := metric_scale_envelope_is_measure hn hc0.
have hregB := caratheodory_limit_borel_regular hmu hc0
  (fun C=>closed_borel_set (compact_closed (@metric_hausdorff R X) (set_valP C).1)).
have hreg := borel_regular_is_regular hm hregB.
pose err j := (j.+1%:R : R)^-1.
have herrpos j : 0<err j by rewrite /err invr_gt0 ltr0n.
have herr1 j : err j<=1.
  have hj : (0<j.+1%:R :> R) by rewrite ltr0n.
  by rewrite /err invf_le1 // ler1n.
have herrsmall e (he : 0<e) : exists N, forall j, (N<=j)%N -> err j<=e.
  have [N hN] := real_reciprocal_below he.
  exists N=> j hNj.
  have hj : (0<j.+1%:R :> R) by rewrite ltr0n.
  have hNp : (0<N.+1%:R :> R) by rewrite ltr0n.
  have hh : err j<=err N by rewrite /err (lef_pV2 hj hNp) ler_nat.
  exact: le_trans hh (ltW hN).
have [Z [u [hZ [hcover [hmem [hbudget hposition]]]]]] := @compact_cost_near_optimal_array R X c hc
  delta nu mu A a r s err hn hmu hbound (fun j=>conj (herrpos j) (herr1 j)) hA.
pose B j := A j `\` Z.
have hBinc i j (hij : (i<=j)%N) : B i `<=` B j by move=> x [hx hxZ]; split=> //; exact: hinc i j hij x hx.
pose K : set (compact_hausdorff_space X) := compact_sets_in_ball a (r+delta).
have hrd : 0<=r+delta by lra.
have hK : compact K := @compact_hausdorff_ball_compact R X a (r+delta) hX hrd.
pose d : compact_metric_set X := exist _ [set a] (mem_set (conj (@compact_set1 X a) (ex_intro _ a erefl))).
have hdK : K d.
  move=> x hx; have hxa : x=a := hx.
  rewrite hxa /metric_closed_ball /= mdistxx; exact hrd.
have [v [hv [hcluster [hdiam hsum]]]] := @compact_cost_limit_array R X c hc K d u delta s err hK hdK hmem hbudget herrsmall.
have hcommon : 0<=s+1 by lra.
have hsmall := @compact_cost_array_uniform_small_diameter R X nat c hc K (s+1) u hK hcommon
  (fun j k C hC=>(hmem j k C hC).1) hposition.
have hres V D hV hVV := @compact_cost_open_residual_bound R X c hc mu B d u v s err
  hmu hreg hBinc hcover hcluster hbudget herrsmall hsmall V D hV hVV.
have hsumfin : (nonnegative_sum setT (fun k=>(masked_compact_cost c (v k))%:E)< +oo)%E :=
  le_lt_trans hsum (ltry s).
have hBbound := @compact_cost_limit_cover_bound R X c hc delta s nu mu (\bigcup_j B j) K v
  hX hd hn hmu hm hreg hK hv hdiam hsumfin hres.
have hdE : (0<delta%:E)%E by rewrite lte_fin.
have hZnu : (nu Z<=0)%E.
  have hh := @caratheodory_limit_upper R X (compact_metric_set X) (fun C=>val C) (fun C=>(c C)%:E)
    mu hmu Z delta%:E nu hdE hn.
  by rewrite hZ in hh.
have hcov : (\bigcup_j A j) `<=` (\bigcup_j B j) `|` Z.
  move=> x [j _ hx]; case: (pselect (Z x))=> hxZ; first by right.
  left; exists j=> //; by split.
have hh := @measure_binary_cover R X nu hnu (\bigcup_j A j) (\bigcup_j B j) Z hcov.
have hfinal := le_trans hh (leeD hBbound hZnu); by rewrite adde0 in hfinal.
Qed.
