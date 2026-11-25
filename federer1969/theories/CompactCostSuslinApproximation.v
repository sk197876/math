(** Federer (1969), 2.10.23, p. 186: apply the coordinate-pruning
    construction of 2.2.12, p. 69, with a fixed-cutoff approximation. Its
    continuity below is supplied by 2.10.22. The closed limit is compact
    inside a supplied compact containing set, and the two-cutoff compact
    inequality of 2.10.20 passes its lower mass bound to the limit. Keeping
    the containing compact explicit avoids changing ambient spaces. Source
    context: IncreasingProjectionLoss.v and CompactCostOpenEnvelope.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactGeneratorCostUP CompactCostContinuityBelow
  CompactCostScaleFinite CompactCostOpenEnvelope LipschitzFunctionCompact MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleCutoffCost CaratheodoryLimitUP MeasureUP MeasureBasic SuslinSetUP SequenceSpace
  CoordinatePruningUP CoordinatePruningBasic MeasurePruningUP ContinuousPruning IncreasingProjectionLoss
  PruningFiniteLoss PruningClosedProjectionLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_suslin_bounded_approximation]: supporting
    compact C and lower mass estimate in
    2.10.23, p. 186. The project uses the
    proved half-error geometric budget of 2.2.12;
    no regularity of the cutoff measure or finite
    final mass is assumed. *)
Theorem compact_cost_suslin_bounded_approximation (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta xi e : R) (nu psi : set X -> \bar R) (S K : set X) :
  metric_boundedly_compact X -> 0<delta -> 0<xi -> xi<delta -> 0<e ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) psi ->
  compact K -> S `<=` K -> is_suslin_set R S ->
  exists C, compact C /\ C `<=` S /\ (nu S-(e/2)%:E<=psi C)%E.
Proof.
move=> hX hd hxi hxd he hn hpsi hK hSK [Z [hZ hZS]].
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := metric_scale_envelope_is_measure hn hc0.
have hcont : has_increasing_set_continuity nu.
  move=> A hA; exact: (@federer_2_10_22 R X c hc delta nu A hX hd hn hA).
have hKfinite := @compact_generator_scale_finite R X c delta nu K hX
  (compact_cost_nonnegative_law hc) hd hn hK.
have hfinite : (nu (fst @` Z)< +oo)%E.
  rewrite hZS; exact: le_lt_trans (@measure_mono R X nu hm S K hSK) hKfinite.
pose choice := @continuous_coordinate_pruning R X nu hm hcont e he Z hfinite.
have hp : is_measure_coordinate_pruning nu Z e choice.1 choice.2 :=
  @continuous_coordinate_pruning_specification R X nu hm hcont e he Z hfinite.
pose F := choice.2.
have hinit : F 0%N=Z := coordinate_pruning_initial (measure_pruning_recursion hp).
pose Cn k := closure (fst @` F k).
pose C := pruned_projection_closed_limit F.
have hKclosed : closed K := compact_closed (@metric_hausdorff R X) hK.
have hprojK k : fst @` F k `<=` K.
  move=> x [p hpF <-]; apply: hSK; rewrite -hZS; exists p=> //.
  have hh := @coordinate_pruning_decreasing R X Z choice.1 F (measure_pruning_recursion hp) 0%N k (leq0n k) p hpF.
  by rewrite hinit in hh.
have hCK k : Cn k `<=` K := fun x hx=>hKclosed _ (closureS (hprojK k) hx).
have hclosed k : closed (Cn k) := @closed_closure X (fst @` F k).
have hCnk k : compact (Cn k) := subclosed_compact (hclosed k) hK (hCK k).
have hdec n m (hnm : (n<=m)%N) : Cn m `<=` Cn n.
  apply: closureS=> x [p hpF <-]; exists p=> //.
  exact: @coordinate_pruning_decreasing R X Z choice.1 F (measure_pruning_recursion hp) n m hnm p hpF.
have hCclosed : closed C := @pruned_projection_limit_closed R X F.
have hCCn : C `<=` Cn 0%N by move=> x hx; exact: hx 0%N Logic.I.
have hC : compact C := subclosed_compact hCclosed (hCnk 0%N) hCCn.
have hCS : C `<=` S.
  rewrite -hZS; exact: pruned_projection_limit_within_original (measure_pruning_recursion hp) hZ.
have hbound k : (nu S-(e/2)%:E<=nu (Cn k))%E.
  have hh := pruning_projection_uniform_lower_bound hp k; rewrite hZS in hh.
  apply: le_trans hh _; apply: (@measure_mono R X nu hm)=> x hx; exact: subset_closure hx.
pose small := metric_scale_envelope (fun D : compact_metric_set X=>val D) (fun D=>(c D)%:E) xi%:E.
have hs := @metric_scale_envelope_specification R X (compact_metric_set X) (fun D=>val D) (fun D=>(c D)%:E) xi%:E.
have hlower := @compact_cost_decreasing_intersection_bound R X c hc xi delta small nu Cn (nu S-(e/2)%:E)%E
  hX hxd hs hn hCnk hdec hbound.
have hxiE : (0<xi%:E)%E by rewrite lte_fin.
have hupper := @caratheodory_limit_upper R X (compact_metric_set X) (fun D=>val D) (fun D=>(c D)%:E)
  psi hpsi C xi%:E small hxiE hs.
exists C; split=> //; split=> //; exact: le_trans hlower hupper.
Qed.
