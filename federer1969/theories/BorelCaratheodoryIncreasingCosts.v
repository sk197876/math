(** Supporting passage from gauge limits to measure limits in Federer
    (1969), 2.10.9, p. 175. Use the all-partition supremum of 2.10.8, p.
    175, and pass finite subsum bounds through increasing limits as in
    2.4.6, p. 84. A common countable Borel hull extends the equality to
    arbitrary targets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  BorelCoverCostUP BorelCaratheodoryMeasure BorelPartition BorelPartitionCoverBounds
  BorelPartitionCharacterization CountableCommonBorelHulls CaratheodoryWeightedComparison
  ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum ExtendedFiniteIncreasingBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_caratheodory_cost_monotone]: supporting
    monotonicity in the gauge for the exponent argument of
    Federer 2.10.9, p. 175, directly from the covering
    definition in 2.10.1, p. 170. All targets are allowed. *)
Lemma borel_caratheodory_cost_monotone (R : realType) (X : metricType R)
    (c d : set X -> \bar R) (hc : is_borel_cover_cost c) (hd : is_borel_cover_cost d) :
  (forall B, borel_set B -> c B<=d B) ->
  forall A, borel_caratheodory_measure c A<=borel_caratheodory_measure d A.
Proof.
move=> hcd A.
have hh := @caratheodory_weighted_generator_comparison R X (@borel_metric_sets R X)
  (fun j => val j) (fun j => c (val j)) (fun j => d (val j))
  (borel_caratheodory_measure c) (borel_caratheodory_measure d) 1
  (borel_caratheodory_specification c) (borel_caratheodory_specification d)
  (fun j => @borel_cover_cost_nonnegative R X c hc (val j) (set_valP j))
  (fun j => @borel_cover_cost_nonnegative R X d hd (val j) (set_valP j)) ltr01
  (fun j => ltac:(rewrite mul1e; exact: hcd (set_valP j))) A.
by rewrite mul1e in hh.
Qed.

(** Source for [borel_caratheodory_increasing_cost_supremum]:
    supporting supremum identity for the exponent limit in
    Federer 2.10.9, p. 175. Nonnegative Borel covering costs
    increase pointwise to a covering cost. On any target,
    their constructed measures have supremum the final measure.
    The arbitrary target need not be Borel or have finite measure. *)
Theorem borel_caratheodory_increasing_cost_supremum (R : realType) (X : metricType R)
    (c : set X -> \bar R) (u : nat -> set X -> \bar R) (D : set X) :
  is_borel_cover_cost c -> (forall k, is_borel_cover_cost (u k)) ->
  countable D -> dense D ->
  (forall B, borel_set B -> extended_increases_to (fun k => u k B) (c B)) ->
  forall A, is_extended_real_supremum
    [set a | exists k, a=borel_caratheodory_measure (u k) A] (borel_caratheodory_measure c A).
Proof.
move=> hc hu hD hden hlim A; constructor.
- move=> a [k ->]; apply: (@borel_caratheodory_cost_monotone R X (u k) c (hu k) hc _ A).
  move=> B hB; apply: (extended_real_supremum_upper (extended_increasing_limit_supremum (hlim B hB))).
  by exists k.
- move=> b hb.
  have hBorel B : borel_set B ->
      (forall k, borel_caratheodory_measure (u k) B<=b) -> borel_caratheodory_measure c B<=b.
    move=> hB hvalues.
    have hs := @borel_partition_cost_supremum_all R X c hc D B hD hden hB.
    apply: (extended_real_supremum_least hs)=> a [H [hH ->]].
    apply: nonnegative_sum_least=> F hF.
    apply: (@nonnegative_increasing_finite_sum_bound R [the eqType of set X] F
      (fun C k => u k C) c b).
    + move=> C hC k; exact: (@borel_cover_cost_nonnegative R X (u k) (hu k) C
        (borel_partition_members hH (hF C hC))).
    + move=> C hC; exact: hlim C (borel_partition_members hH (hF C hC)).
    + move=> k; apply: le_trans (@nonnegative_sum_upper R [the choiceType of set X] H (u k) F hF) _.
      exact: le_trans (@borel_partition_cost_upper R X (u k) (hu k) B H hH) (hvalues k).
  have [B [hAB [hB he]]] := @countable_common_borel_hull R X
    (fun k => borel_caratheodory_measure (u k)) A
    (fun k => borel_caratheodory_is_measure (hu k))
    (fun k => borel_caratheodory_borel_regular (hu k)).
  apply: le_trans (@measure_mono R X (borel_caratheodory_measure c)
    (borel_caratheodory_is_measure hc) A B hAB) _.
  apply: hBorel hB _=> k; rewrite -(he k); apply: hb; by exists k.
Qed.

(** Source for [borel_caratheodory_increasing_cost_limit]: supporting
    increasing convergence of independently constructed measures in
    Federer 2.10.9, p. 175. The conclusion includes both
    measure monotonicity and the extended-real order limit. *)
Theorem borel_caratheodory_increasing_cost_limit (R : realType) (X : metricType R)
    (c : set X -> \bar R) (u : nat -> set X -> \bar R) (D : set X) :
  is_borel_cover_cost c -> (forall k, is_borel_cover_cost (u k)) ->
  countable D -> dense D ->
  (forall B, borel_set B -> extended_increases_to (fun k => u k B) (c B)) ->
  forall A, extended_increases_to (fun k => borel_caratheodory_measure (u k) A)
    (borel_caratheodory_measure c A).
Proof.
move=> hc hu hD hden hl A.
apply: extended_increasing_supremum_limit.
- move=> k l hkl; apply: (@borel_caratheodory_cost_monotone R X (u k) (u l) (hu k) (hu l) _ A).
  move=> B hB; exact: (hl B hB).1 k l hkl.
- exact: (@borel_caratheodory_increasing_cost_supremum R X c u D hc hu hD hden hl A).
Qed.
