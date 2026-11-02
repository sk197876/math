(** Passage from bounded separation to the full test-set inequality in
    Federer (1969), 2.9.6, p. 155, using 2.3.2(7), pp. 74–75. Apply
    countable additivity to restrictions, so test sets need not be
    measurable and infinite values are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  CoveringFamilyUP BoundedBorelPartitionUP BoundedBorelPartition
  MeasureDisjointIntersectionSum NonnegativeSum NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_separation_from_bounded_cells]: supporting
    bounded-to-global step in Federer 2.9.6, p. 155 The Borel regular
    measure is tested on arbitrary A,B,T, using the same disjoint bounded
    cells in all three sums. *)
Lemma measure_separation_from_bounded_cells (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A B T : set X) :
  is_measure phi -> is_borel_regular_measure phi ->
  (forall K, borel_set K -> metric_set_bounded K ->
    phi (A `&` K)+phi (B `&` K)<=phi (T `&` K)) ->
  phi A+phi B<=phi T.
Proof.
move=> hm hr hlocal.
have [P hP] := @bounded_borel_partition_exists R X.
have hPm n : measure_measurable phi (P n) := @borel_regular_borel_measurable R X phi hm hr (P n)
  (bounded_borel_partition_borel hP n).
have hsum S : phi S=nonnegative_sum setT (fun n => phi (P n `&` S)).
  have h := @measure_disjoint_union_intersection_sum R X phi P hm hPm
    (bounded_borel_partition_disjoint hP) S.
  by rewrite (bounded_borel_partition_union hP) setTI in h.
rewrite (hsum A) (hsum B) (hsum T).
rewrite -(@nonnegative_sum_add R _ (@setT nat)
  (fun n => phi (P n `&` A)) (fun n => phi (P n `&` B))
  (fun n _ => measure_nonnegative hm _) (fun n _ => measure_nonnegative hm _)).
apply: nonnegative_sum_mono=> n _.
have h := hlocal (P n) (bounded_borel_partition_borel hP n) (bounded_borel_partition_bounded hP n).
by rewrite (setIC A (P n)) (setIC B (P n)) (setIC T (P n)) in h.
Qed.
