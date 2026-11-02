(** Localisation of null exceptional sets in Federer (1969), 2.9.5, p. 155:
    prove nullity on every bounded subset, then exhaust the metric space by
    countably many bounded sets. The existing abstract bounded Borel
    partition supplies this exhaustion, including the empty ambient space.
    both original class-M measures are finite on our bounded cells. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic CoveringFamilyUP MetricDiameter
  BoundedBorelPartitionUP BoundedBorelPartition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_null_of_bounded_subsets]: supporting
    final inferences phi(Q)=0 and phi(R(a,b))=0 in
    Federer 2.9.5, p. 155. Neither the
    exceptional set nor its intersections with bounded cells
    are assumed measurable. *)
Lemma measure_null_of_bounded_subsets (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (E : set X) :
  is_measure phi ->
  (forall A, metric_set_bounded A -> A `<=` E -> phi A=0) -> phi E=0.
Proof.
move=> hm hlocal.
have [P hP] := @bounded_borel_partition_exists R X.
have hbounded n : metric_set_bounded (E `&` P n).
  apply: le_lt_trans (@extended_metric_diameter_mono R X (E `&` P n) (P n)
    (fun x hx => hx.2)) _.
  exact: bounded_borel_partition_bounded hP n.
have hz n : phi (E `&` P n)=0 := hlocal _ (hbounded n) (fun x hx => hx.1).
have he : (\bigcup_n (E `&` P n))=E.
  apply/seteqP; split=> [x [n _ [hx _]]|x hx] //.
  have hcover : (\bigcup_n P n) x by rewrite (bounded_borel_partition_union hP).
  have [n _ hn] := hcover; exists n=> //; by split.
rewrite -he; exact (@measure_null_countable_union R X _ phi hm (@setT nat)
  (fun n => E `&` P n) (countableP _) (fun n _ => hz n)).
Qed.
