(** Finite-subsum lower bounds for the multiplicity limit in Federer (1969),
    2.10.10, p. 176, supporting the functional of 2.5.10, p. 101. Every
    finite collection of fibre points is separated by some sufficiently fine
    partition, giving the finite lower bounds that determine its counting
    measure by 2.1.1(3), p. 52. the proof below develops the finite-subset
    step explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ClosedCoverTreeUP CoverPartitionTreeUP
  FinitePartitionSeparation PartitionHitCounts CountingMeasure CountingInjectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.
Local Open Scope ereal_scope.

(** Source for [partition_hit_count_finite_lower_bound]:
    every finite collection of points contributes that many
    distinct cells at some level, the finite-subsum step
    in Federer 2.10.10, p. 176. The set
    need not be measurable for this combinatorial assertion. *)
Lemma partition_hit_count_finite_lower_bound (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) (A : set X) (B : {fset X}) :
  (forall x, x \in B -> A x) ->
  exists n, counting_measure (R:=R) [set` B]<=@partition_hit_count R X P A n.
Proof.
move=> hB; have [n [g [hg hinj]]] := @finite_points_partition_separation R X E P hE hP B.
exists n.+1.
apply: (@counting_measure_injection_bound R X [the choiceType of (seq nat : Type)]
  [set` B] (partition_hit_indices P A n.+1) g).
- move=> x hx; split; first exact: (hg x).1.
  exists x; split; [exact: hB hx|exact: (hg x).2].
- move=> x y hx hy he; exact: hinj x y hx hy he.
Qed.
