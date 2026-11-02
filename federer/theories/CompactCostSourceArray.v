(** Federer (1969), 2.10.22, p. 184: assemble the near-optimal source
    covers. The union of all zero-cost exceptions is null for the final
    measure. The common finite cost bound yields one uniform late-diameter
    bound for every row. Source context and the explicit treatment of finite
    covers: CompactCostCoverRow.v and CompactGeneratorCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactMetricBounded CompactBallProfiles
  CompactGeneratorCostUP CompactCostCoverRow MetricClosedBalls MetricScaleEnvelopeUP
  MetricScaleOptionalCover CaratheodoryLimitUP CaratheodoryLimitMeasure MeasureUP MeasureBasic
  MeasureIndexedCover NonnegativeSum SummableCostEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_near_optimal_array]: supporting
    compact-cover array in 2.10.22, p. 184.
    One final-measure-null exceptional set suffices for
    all rows, with no measurability assumption on the
    increasing targets themselves. *)
Theorem compact_cost_near_optimal_array (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (delta : R) (nu mu : set X -> \bar R) (A : nat -> set X) (a : X) (r s : R)
    (err : nat -> R) :
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E nu ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) mu ->
  (forall j, (nu (A j)<=s%:E)%E) -> (forall j, 0<err j /\ err j<=1) ->
  (forall j, A j `<=` metric_closed_ball a r) ->
  exists (Z : set X) (u : nat -> nat -> option (compact_metric_set X)),
    mu Z=0%E /\ (forall j, A j `\` Z `<=` \bigcup_k optional_generator_set (fun C=>val C) (u j k)) /\
    (forall j k C, u j k=Some C -> compact_sets_in_ball a (r+delta) C /\ compact_metric_diameter C<=delta) /\
    (forall j, (nonnegative_sum setT (fun k=>(optional_generator_cost c (u j k))%:E)<=(s+err j)%:E)%E) /\
    (forall j k, k.+1%:R*optional_generator_cost c (u j k)<=s+1).
Proof.
move=> hn hmu hbound herr hA.
have hex j := @compact_cost_near_optimal_row R X c hc delta nu mu (A j) a r s (err j)
  hn hmu (hbound j) (herr j).1 (herr j).2 (hA j).
pose Z0 j := projT1 (cid (hex j)).
pose u j := projT1 (cid (projT2 (cid (hex j)))).
have hrow j : mu (Z0 j)=0%E /\
    A j `\` Z0 j `<=` \bigcup_k optional_generator_set (fun C=>val C) (u j k) /\
    (forall k C, u j k=Some C -> compact_sets_in_ball a (r+delta) C /\ compact_metric_diameter C<=delta) /\
    (nonnegative_sum setT (fun k=>(optional_generator_cost c (u j k))%:E)<=(s+err j)%:E)%E /\
    (forall k, k.+1%:R*optional_generator_cost c (u j k)<=s+1).
  exact: projT2 (cid (projT2 (cid (hex j)))).
pose Z := \bigcup_j Z0 j.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := caratheodory_limit_is_measure hmu hc0.
have hZ : mu Z=0%E.
  have hh := @measure_indexed_cover R X [the choiceType of (nat : Type)] mu hm Z setT Z0
    (countableP _) (fun x hx=>hx).
  have hz : nonnegative_sum setT (fun j=>mu (Z0 j))=0%E.
    apply: nonnegative_sum_zero=> j _; exact: (hrow j).1.
  rewrite hz in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm Z).
exists Z,u; split=> //; split.
- move=> j x [hx hxZ]; apply: (hrow j).2.1; split=> // hxZ0.
  apply: hxZ; by exists j.
- split; first by move=> j; exact: (hrow j).2.2.1.
  split; [by move=> j; exact: (hrow j).2.2.2.1|by move=> j; exact: (hrow j).2.2.2.2].
Qed.
