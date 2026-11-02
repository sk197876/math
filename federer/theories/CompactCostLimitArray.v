(** Federer (1969), 2.10.22, pp. 184–185:
    extract the limiting cover positions and bound
    their total cost by s. The compact factor has
    an activity flag, so finite covers require no
    artificial positive-cost padding. The extraction uses
    the general-topology cluster formulation described in
    CompactArrayCluster.v; cost-ordering is explained in
    SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactGeneratorCostUP CompactGeneratorCostLaws MaskedCompactGenerators CompactArrayCluster
  ArrayClusterCost ArrayClusterClosed NonnegativeSum NonnegativeSumSupport SummableCostEnumerationUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_limit_array]: supporting
    D_k extraction, admissibility and total-cost bound
    t<=s in 2.10.22, pp. 184–185.
    The ambient compact family and the original finite
    costs remain explicit; no target measurability is used. *)
Theorem compact_cost_limit_array (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (K : set (compact_hausdorff_space X)) (d : compact_metric_set X)
    (u : nat -> nat -> option (compact_metric_set X)) (delta s : R) (err : nat -> R) :
  compact K -> K d ->
  (forall j k C, u j k=Some C -> K C /\ compact_metric_diameter C<=delta) ->
  (forall j, (nonnegative_sum setT (fun k=>(optional_generator_cost c (u j k))%:E)<=(s+err j)%:E)%E) ->
  (forall e : R, 0<e -> exists N, forall j, (N<=j)%N -> err j<=e) ->
  exists v : nat -> bool*compact_hausdorff_space X,
    (forall k, K (v k).2) /\
    is_countable_array_cluster (fun j k=>optional_compact_point d (u j k)) v /\
    (forall k, (v k).1 -> compact_metric_diameter (v k).2<=delta) /\
    (nonnegative_sum setT (fun k=>(masked_compact_cost c (v k))%:E)<=s%:E)%E.
Proof.
move=> hK hd hmem hbudget herr.
pose P := [the topologicalType of (bool*compact_hausdorff_space X)%type].
pose q j : prod_topology (fun _ : nat => P) := fun k=>optional_compact_point d (u j k).
pose B : set P := [set p | K p.2].
have hB : compact B := compact_flagged_family hK.
have hq j k : B (q j k).
  rewrite /B /q /optional_compact_point; case he: (u j k)=> [C|] //.
  exact: (hmem j k C he).1.
have [v [hv hcluster]] := compact_countable_array_cluster hB hq.
have hcl : is_countable_array_cluster q v := hcluster.
have hcost : continuous (fun p : P => (masked_compact_cost c p : real_line_metric R)) :=
  masked_compact_cost_continuous (compact_cost_continuous_law hc).
have h0 j k : 0<=masked_compact_cost c (q j k).
  rewrite /masked_compact_cost; case: (q j k).1=> //.
  exact: compact_cost_nonnegative_law hc (q j k).2.
have hbud j : (nonnegative_sum setT (fun k=>(masked_compact_cost c (q j k))%:E)<=(s+err j)%:E)%E.
  have he : nonnegative_sum setT (fun k=>(masked_compact_cost c (q j k))%:E)=
      nonnegative_sum setT (fun k=>(optional_generator_cost c (u j k))%:E).
    apply: nonnegative_sum_ext=> k _; by rewrite /q optional_compact_costE.
  by rewrite he.
have hdiamcl : closed [set C : compact_hausdorff_space X | compact_metric_diameter C<=delta].
  apply: (@preimage_closed [the topologicalType of compact_hausdorff_space X] (real_line_metric R)
    (fun C=>compact_metric_diameter C) [set x | x<=delta]).
  - move=> C hC; exact: compact_diameter_map_continuous.
  - exact: closed_le.
have hdiam k : (v k).1 -> compact_metric_diameter (v k).2<=delta.
  change ([set p : P | p.1 -> compact_metric_diameter p.2<=delta] (v k)).
  apply: (@array_cluster_closed_coordinate P q v [set p : P | p.1 -> compact_metric_diameter p.2<=delta] 0%N k hcl
    (@flagged_closed_condition [the topologicalType of compact_hausdorff_space X]
      [set C | compact_metric_diameter C<=delta] hdiamcl)).
  move=> j hj; rewrite /q /optional_compact_point; case he: (u j k)=> [C|] // _.
  exact: (hmem j k C he).2.
have hsum : (nonnegative_sum setT (fun k=>(masked_compact_cost c (v k))%:E)<=s%:E)%E.
  apply: nonnegative_sum_least=> D _; rewrite sumEFin lee_fin.
  exact: (@array_cluster_finite_cost_bound R P (masked_compact_cost c) q v s err hcost hcl h0 hbud herr D).
exists v; by split=> //; split=> //; split.
Qed.
