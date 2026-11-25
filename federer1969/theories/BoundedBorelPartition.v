(** Existence of the partition used in Federer (1969), 2.9.2, p. 153.
    Increasing closed balls exhaust a nonempty metric space; the already
    proved sequence disjointification supplies the pieces. For an empty
    space, the constant empty sequence suffices. No separability or
    inhabitedness premise is added. Source context:
    BoundedBorelPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BoundedBorelPartitionUP CoveringFamilyUP CoveringFamilyLaws
  MetricClosedBalls MetricDiameter SetSequenceDisjointification TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_borel_partition_exists]: supporting
    existence of the bounded disjoint Borel pieces used in
    Federer 2.9.2, p. 153. The concrete ball
    sequence is confined to this opaque proof; downstream
    arguments use only the partition's abstract laws. *)
Theorem bounded_borel_partition_exists (R : realType) (X : metricType R) :
  exists P : nat -> set X, @is_bounded_borel_partition R X P.
Proof.
case: (pselect (@setT X !=set0))=> [[a _]|hempty].
- pose F n := metric_closed_ball a (n.+1%:R : R)%R.
  exists (set_sequence_disjointify F); constructor.
  + move=> n; apply: borel_set_difference; first exact (@closed_borel_set X (F n) (@metric_closed_ball_closed R X a (n.+1%:R : R)%R)).
    apply: borel_set_countable_union; first exact: countableP.
    move=> k _; exact (@closed_borel_set X (F k) (@metric_closed_ball_closed R X a (k.+1%:R : R)%R)).
  + move=> n; apply: le_lt_trans (@extended_metric_diameter_mono R X
      (set_sequence_disjointify F n) (F n) (fun x hx => hx.1)) _.
    exact (@covering_closed_ball_bounded R X a (n.+1%:R : R)%R (ler0n _ _)).
  + rewrite set_sequence_disjointify_union; apply/seteqP; split=> [x _|x _]; first exact I.
    pose n := Num.bound (mdist a x).
    have hn : (mdist a x<n%:R)%R := archi_boundP (mdist_ge0 a x).
    exists n=> //; apply: le_trans (ltW hn) _; by rewrite ler_nat.
  + exact: set_sequence_disjointify_disjoint.
- exists (fun _ : nat => @set0 X); constructor.
  + by move=> n; exact: open_borel_set open0.
  + by move=> n; rewrite /metric_set_bounded extended_metric_diameter_empty ltry.
  + apply/seteqP; split=> [x [n _ []]|x _]; exfalso; apply: hempty; by exists x.
  + by move=> n m h x [].
Qed.
