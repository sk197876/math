(** Private existence proof for Federer 2.3.5, p. 76: disjointify a
    countable small closed cover. Source context and the diameter
    convention: SmallBorelPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import SmallBorelPartitionUP SeparableClosedCover
  SetSequenceDisjointification TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [small_borel_partition_exists]: construction of the partition
    in Federer 2.3.5, p. 76. *)
Lemma small_borel_partition_exists (R : realType) (Y : metricType R)
    (D : set Y) (e : R) : countable D -> dense D -> 0 < e ->
  exists B : nat -> set Y, is_small_borel_partition e B.
Proof.
move=> hc hd he; case: (pselect (@setT Y !=set0))=> [hn|hn].
- have [F [hF hcover]] := @separable_closed_small_cover R Y D setT e hc hd closedT hn he.
  exists (set_sequence_disjointify F); constructor.
  + move=> n; apply: borel_set_difference; first exact: closed_borel_set (hF n).1.
    apply: borel_set_countable_union; first exact: countableP.
    by move=> k _; exact: closed_borel_set (hF k).1.
  + by rewrite set_sequence_disjointify_union -hcover.
  + exact: set_sequence_disjointify_disjoint.
  + move=> n x y [hx _] [hy _]; exact: (hF n).2.2.2 x y hx hy.
- exists (fun _ => set0); constructor.
  + move=> n; exact: open_borel_set open0.
  + apply/seteqP; split=> [y [n _ []]|y _]; exfalso; apply: hn; by exists y.
  + by move=> n m h y [].
  + by move=> n x y [].
Qed.
