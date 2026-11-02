(** Supporting the slicing identities of Federer (1969), 2.10.16, p. 178,
    via the partition proof of 2.10.8–2.10.10, pp. 175–176, extended to
    Suslin source sets. The extra hypotheses explicitly provide Borel cost
    hulls and the cost lower bound on Suslin sets; neither is assumed
    without proof for the applications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum TopologicalBorel BorelFamilyBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic BorelImageTreeEquality
  ShrinkingBorelPartitionLevels MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  MetricScaleIndexedCover BorelCoverCostUP BorelCaratheodoryMeasure
  BorelPartitionCostLimits CaratheodoryLimitUP ExtendedRealBoundsUP
  SuslinSetUP BorelClosedProjection BorelSuslinImages SuslinMeasurability
  BorelRegularMeasureUP MeasureUP MeasureDisjointSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.


(** Source for [suslin_partition_cell]: supporting Suslin-cell
    property for the partition argument behind 2.10.16, p. 178;
    an intersection with a Borel partition member remains Suslin
    by 2.2.10, p. 66. *)
Lemma suslin_partition_cell (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A s :
  is_suslin_set R A -> is_suslin_set R (A `&` P s).
Proof.
move=> hA; apply: suslin_binary_intersection hA _.
exact: metric_borel_suslin (@cover_partition_borel R X E P hE hP s).
Qed.

(** Source for [suslin_partition_level_cost_upper]: supporting
    lower partition bound for 2.10.16, p. 178, following
    2.10.8, p. 175. Suslin cells are measurable by 2.2.12,
    pp. 68–69; the cost bound is an explicit premise. *)
Lemma suslin_partition_level_cost_upper (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hlow : forall S, is_suslin_set R S -> c S<=borel_caratheodory_measure c S)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n : is_suslin_set R A ->
  borel_partition_level_cost c P A n<=borel_caratheodory_measure c A.
Proof.
move=> hA; pose psi := borel_caratheodory_measure c.
have hm := borel_caratheodory_is_measure hc.
have hreg := borel_caratheodory_borel_regular hc.
apply: le_trans (_ : nonnegative_sum [set s | size s=n] (fun s => psi (A `&` P s))<=_).
- apply: nonnegative_sum_mono=> s hs; exact: hlow ((@suslin_partition_cell R X E P hE hP A s hA)).
- apply: (@measure_disjoint_sum_bound R X [the choiceType of (seq nat : Type)] psi
    hm A [set s | size s=n] (fun s => A `&` P s)).
  + by move=> s hs x [hx _].
  + move=> s hs; apply: (@suslin_set_measurable R X psi hm (A `&` P s)).
    * move=> C hC; exact (@borel_regular_borel_measurable R X psi hm hreg C (closed_borel_set hC)).
    * exact: (@suslin_partition_cell R X E P hE hP A s hA).
  + move=> s t hs ht hst; apply/seteqP; split=> x; last by [].
    move=> [[hx hxs] [_ hxt]]; exfalso; apply: hst.
    apply: (@cover_partition_level_unique X E P hP s t x _ hxs hxt).
    by rewrite hs ht.
Qed.

(** Source for [suslin_partition_level_scale_bound]: supporting
    upper partition bound for 2.10.16, p. 178. Replace every
    Suslin cell by its explicitly supplied Borel cost hull and
    use the defining cover bound of 2.10.1, p. 170. *)
Lemma suslin_partition_level_scale_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hhull : forall S, is_suslin_set R S -> exists C,
      borel_set C /\ S `<=` C /\ extended_metric_diameter C<=extended_metric_diameter S /\ c C<=c S)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A n delta nu :
  is_suslin_set R A ->
  @is_metric_scale_envelope R X (@borel_metric_sets R X)
    (fun j => val j) (fun j => c (val j)) delta nu ->
  (@closed_cover_tree_scale R n.+1)%:E<=delta ->
  nu A<=borel_partition_level_cost c P A n.+1.
Proof.
move=> hA hn hd.
have hex s := hhull _ ((@suslin_partition_cell R X E P hE hP A s hA)).
pose C s := projT1 (cid (hex s)).
have hC s : borel_set (C s) /\ A `&` P s `<=` C s /\
    extended_metric_diameter (C s)<=extended_metric_diameter (A `&` P s) /\ c (C s)<=c (A `&` P s)
  := projT2 (cid (hex s)).
pose u s : @borel_metric_sets R X := Sub (C s) (mem_set (hC s).1).
apply: le_trans (_ : nonnegative_sum [set s | size s=n.+1] (fun s => c (C s))<=_).
- apply: (@metric_scale_envelope_indexed_cover R X (@borel_metric_sets R X)
    [the choiceType of (seq nat : Type)] (fun j => val j) (fun j => c (val j))
    delta nu hn A [set s | size s=n.+1] u (cover_partition_level_countable n.+1)).
  + move=> s hs; exact (@borel_cover_cost_nonnegative R X c hc (C s) (hC s).1).
  + move=> s hs; apply: le_trans (hC s).2.2.1 _.
    apply: le_trans (_ : extended_metric_diameter (A `&` P s)<=(@closed_cover_tree_scale R n.+1)%:E) hd.
    apply: (metric_diameter_least (extended_metric_diameter_specification (A `&` P s))).
    * rewrite lee_fin; exact: ltW (closed_cover_tree_scale_positive R n.+1).
    * move=> x y [_ hx] [_ hy]; rewrite lee_fin.
      have hne : s !=[::] by rewrite -size_eq0 hs.
      have h := @cover_partition_level_diameter R X E P hE hP s x y hne hx hy.
      by rewrite hs in h.
  + move=> x hx; have [s [hs hxs]] := @cover_partition_level_membership R X E P hE hP x n.+1.
    exists s=> //; exact: (hC s).2.1 _ (conj hx hxs).
- apply: nonnegative_sum_mono=> s hs; exact: (hC s).2.2.2.
Qed.

(** Source for [suslin_partition_cost_supremum]: supporting
    Suslin version of the shrinking-partition identity in
    2.10.8–2.10.10, pp. 175–176, used for the projected
    Suslin images in 2.10.16, p. 178. Borel replacement
    and the cost bound remain explicit proved prerequisites. *)
Theorem suslin_partition_cost_supremum (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (hlow : forall S, is_suslin_set R S -> c S<=borel_caratheodory_measure c S)
    (hhull : forall S, is_suslin_set R S -> exists C,
      borel_set C /\ S `<=` C /\ extended_metric_diameter C<=extended_metric_diameter S /\ c C<=c S)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) A : is_suslin_set R A ->
  is_extended_real_supremum [set a | exists n, a=borel_partition_level_cost c P A n]
    (borel_caratheodory_measure c A).
Proof.
move=> hA; constructor.
- move=> a [n ->]; exact (@suslin_partition_level_cost_upper R X c hc hlow E P hE hP A n hA).
- move=> b hb; apply: (caratheodory_limit_least (borel_caratheodory_specification c))=> delta nu hp hn.
  have hex : exists n, (@closed_cover_tree_scale R n.+1)%:E<=delta.
    clear hn; case: delta hp=> [d| |] hp.
    + rewrite lte_fin in hp; have [n hn] := closed_cover_tree_scale_small hp.
      exists n; rewrite lee_fin; exact: ltW hn.
    + exists 0%N; exact: leey.
    + by move: hp; rewrite ltNge leNye.
  have [n hd] := hex.
  apply: le_trans (@suslin_partition_level_scale_bound R X c hc hhull E P hE hP A n delta nu hA hn hd) _.
  apply: hb; by exists n.+1.
Qed.
