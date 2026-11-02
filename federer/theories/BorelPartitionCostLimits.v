(** The partition characterization in Federer (1969), 2.10.8, p. 175, for
    the shrinking nested partitions used in 2.10.10, p. 176. We prove that
    their cost sums have supremum equal to the constructed measure of each
    Borel set. This is the particular partition system needed for 2.5.10, p.
    101, not a claim that every alternative partition characterization has
    been formalised. Source context: BorelCoverCostUP.v and
    ShrinkingBorelPartitionLevels.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel BorelFamilyBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic BorelImageTreeEquality
  ShrinkingBorelPartitionLevels MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleIndexedCover BorelCoverCostUP BorelCaratheodoryMeasure
  BorelCostPartitionBound CaratheodoryLimitUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_partition_level_cost]: the cost
    sum over one small Borel partition in Federer 2.10.8,
    p. 175, as used in 2.10.10, p. 176.
    Empty indexed cells are permitted and have zero cost
    by the covering-cost law. *)
Definition borel_partition_level_cost (R : realType) (X : Type)
    (c : set X -> \bar R) (P : seq nat -> set X) (A : set X) n :=
  nonnegative_sum [set s | size s=n] (fun s => c (A `&` P s)).

(** Source for [borel_partition_level_cost_upper]: the
    disjoint-piece inequality in the proof of Federer
    2.10.8, p. 175, for the nested partitions
    in 2.10.10, p. 176. *)
Lemma borel_partition_level_cost_upper (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n : borel_set A ->
  borel_partition_level_cost c P A n<=borel_caratheodory_measure c A.
Proof.
move=> hA; apply: (@borel_cost_disjoint_sum_bound R X c hc
  [the choiceType of (seq nat : Type)] [set s | size s=n] (fun s => A `&` P s) A).
- move=> s hs; apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X))=> //.
  exact (@cover_partition_borel R X E P hE hP s).
- by move=> s hs x [hx _].
- move=> s t hs ht hst; apply/seteqP; split=> x; last by [].
  move=> [[hx hxs] [_ hxt]]; exfalso; apply: hst.
  apply: (@cover_partition_level_unique X E P hP s t x _ hxs hxt).
  by rewrite hs ht.
Qed.

(** Source for [borel_partition_level_scale_bound]: a
    sufficiently fine partition is an admissible cover for
    a size approximation, the last inequality in Federer
    2.10.8, p. 175, used in 2.10.10,
    p. 176. The level is positive, since the
    root need not have bounded diameter. *)
Lemma borel_partition_level_scale_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n delta nu :
  borel_set A ->
  @is_metric_scale_envelope R X (@borel_metric_sets R X)
    (fun j => val j) (fun j => c (val j)) delta nu ->
  (@closed_cover_tree_scale R n.+1)%:E<=delta ->
  nu A<=borel_partition_level_cost c P A n.+1.
Proof.
move=> hA hn hd.
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X))=> //.
  exact (@cover_partition_borel R X E P hE hP s).
pose u s : @borel_metric_sets R X := Sub (A `&` P s) (mem_set (hS s)).
apply: (@metric_scale_envelope_indexed_cover R X (@borel_metric_sets R X)
  [the choiceType of (seq nat : Type)] (fun j => val j) (fun j => c (val j))
  delta nu hn A [set s | size s=n.+1] u (cover_partition_level_countable n.+1)).
- move=> s hs; exact (@borel_cover_cost_nonnegative R X c hc (A `&` P s) (hS s)).
- move=> s hs; apply: le_trans (_ : extended_metric_diameter (A `&` P s)<=(@closed_cover_tree_scale R n.+1)%:E) hd.
  apply: (metric_diameter_least (extended_metric_diameter_specification (A `&` P s))).
  + rewrite lee_fin; exact: ltW (closed_cover_tree_scale_positive R n.+1).
  + move=> x y [_ hx] [_ hy]; rewrite lee_fin.
    have hne : s !=[::] by rewrite -size_eq0 hs.
    have h := @cover_partition_level_diameter R X E P hE hP s x y hne hx hy.
    by rewrite hs in h.
- move=> x hx; have [s [hs hxs]] := @cover_partition_level_membership R X E P hE hP x n.+1.
  exists s=> //; by split.
Qed.

(** Source for [borel_partition_cost_supremum]: the
    small-partition cost characterization of Federer 2.10.8,
    p. 175, specialized to the nested system used
    in 2.10.10, p. 176. It includes zero
    and infinite measure values. *)
Theorem borel_partition_cost_supremum (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A : borel_set A ->
  is_extended_real_supremum [set a | exists n, a=borel_partition_level_cost c P A n]
    (borel_caratheodory_measure c A).
Proof.
move=> hA; constructor.
- move=> a [n ->]; exact (@borel_partition_level_cost_upper R X c hc E P hE hP A n hA).
- move=> b hb; apply: (caratheodory_limit_least (borel_caratheodory_specification c))=> delta nu hp hn.
  have hex : exists n, (@closed_cover_tree_scale R n.+1)%:E<=delta.
    clear hn; case: delta hp=> [d| |] hp.
    + rewrite lte_fin in hp; have [n hn] := closed_cover_tree_scale_small hp.
      exists n; rewrite lee_fin; exact: ltW hn.
    + exists 0%N; exact: leey.
    + by move: hp; rewrite ltNge leNye.
  have [n hd] := hex.
  apply: le_trans (@borel_partition_level_scale_bound R X c hc E P hE hP A n delta nu hA hn hd) _.
  apply: hb; by exists n.+1.
Qed.
