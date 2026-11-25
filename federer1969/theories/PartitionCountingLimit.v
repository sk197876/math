(** The combinatorial limit in Federer (1969), 2.10.10, p. 176: the
    increasing number of small partition cells meeting a set tends to its
    counting measure. Applied to a fibre, this is the pointwise limit needed
    for the functional in 2.5.10, p. 101. The finite-subsum interpretation
    is 2.1.1(3), p. 52. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ClosedCoverTreeUP CoverPartitionTreeUP
  PartitionHitCounts PartitionHitFiniteLowerBound CountingMeasure
  NonnegativeSum ExtendedRealBoundsUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.
Local Open Scope ereal_scope.

(** Source for [partition_hit_count_supremum]: the
    finite-subsum characterization identifies the supremum
    of partition counts with counting measure, supporting
    Federer 2.10.10, p. 176. No assumption
    that the fibre is finite or countable is imposed. *)
Lemma partition_hit_count_supremum (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) (A : set X) :
  is_extended_real_supremum
    [set a | exists n, a=@partition_hit_count R X P A n]
    (counting_measure (R:=R) A).
Proof.
constructor.
- move=> a [n ->]; exact (@partition_hit_count_upper R X E P hP A n).
- move=> b hb; rewrite counting_measure_sum.
  apply: nonnegative_sum_least=> B hB.
  have [n hn] := @partition_hit_count_finite_lower_bound R X E P hE hP A B hB.
  have hcb : counting_measure (R:=R) [set` B]<=b.
    apply: le_trans hn _; apply: hb; by exists n.
  have hsum : (\sum_(x <- B) (1:R)%:E)=counting_measure (R:=R) [set` B].
    by rewrite counting_measure_sum nonnegative_sum_finite.
  by rewrite hsum.
Qed.

(** Source for [partition_hit_count_limit]: direct
    combinatorial part of the increasing multiplicity assertion
    in Federer 2.10.10, p. 176. The
    conclusion is convergence in the extended-real order
    topology, including an infinite limit. *)
Theorem partition_hit_count_limit (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) (A : set X) :
  extended_increases_to (@partition_hit_count R X P A) (counting_measure (R:=R) A).
Proof.
apply: extended_increasing_supremum_limit.
- apply: (@homo_leq (\bar R) (@partition_hit_count R X P A)
    (fun a b => is_true (a<=b)) (fun a => lexx a)
    (fun a b c hab hbc => le_trans hab hbc)).
  move=> n; exact (@partition_hit_count_increasing R X E P hE hP A n).
- exact (@partition_hit_count_supremum R X E P hE hP A).
Qed.
