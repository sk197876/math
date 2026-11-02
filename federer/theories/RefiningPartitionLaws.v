(** Supporting partition laws for Federer (1969), 2.8.19, p. 152. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality topology.
From Federer Require Import BorelPartition CountablyClosedFamilyUP RefiningBorelPartitionsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partition_cells_meeting_equal]: the same-level case of the
    maximal-member argument in Federer 2.8.19, p. 152 Two cells meeting at a
    point are equal by disjointness. *)
Lemma partition_cells_meeting_equal (X : topologicalType) (P : set (set X)) S T x :
  is_borel_partition setT P -> P S -> P T -> S x -> T x -> S = T.
Proof.
move=> hp hS hT hx hy; apply: contrapT=> hne.
have hd := @borel_partition_disjoint X setT P hp S T hS hT hne.
have hh : (S `&` T) x by split.
by rewrite hd in hh.
Qed.

(** Source for [partition_level_point_cell]: the point
    coverage clause used in Federer 2.8.19, p. 152,
    from the partition definition of 2.2.1, p. 60. *)
Lemma partition_level_point_cell (X : topologicalType) (P : nat -> set (set X)) :
  is_refining_borel_partitions P -> forall n x, exists S, P n S /\ S x.
Proof.
move=> hp n x.
have hx : (\bigcup_(S in P n) S) x by rewrite (borel_partition_union (refining_partition_levels hp n)).
by have [S hS hxS] := hx; exists S.
Qed.

(** Source for [partition_successor_meeting_subset]: Supporting Federer
    2.8.19, p. 152.A child meeting a parent equals one of the parent's
    covering children. *)
Lemma partition_successor_meeting_subset (X : topologicalType) (P : nat -> set (set X)) :
  is_refining_borel_partitions P -> forall n S T x,
    P n S -> P n.+1 T -> S x -> T x -> T `<=` S.
Proof.
move=> hp n S T x hS hT hx hy.
have [H [hH hU]] := @refining_partition_successor X P hp n S hS.
have hxH : (\bigcup_(U in H) U) x by rewrite hU.
have [U hUH hxU] := hxH.
have he := @partition_cells_meeting_equal X (P n.+1) T U x
  (refining_partition_levels hp n.+1) hT (hH U hUH) hy hxU.
move=> y hyT; rewrite -hU; exists U=> //; by rewrite -he.
Qed.

(** Source for [partition_finer_meeting_subset]: the nested cells assertion
    needed in Federer 2.8.19, p. 152 This induction uses only the original
    one-step union laws. *)
Lemma partition_finer_meeting_subset (X : topologicalType) (P : nat -> set (set X)) :
  is_refining_borel_partitions P -> forall i j S T x,
    (i <= j)%N -> P i S -> P j T -> S x -> T x -> T `<=` S.
Proof.
move=> hp i j; elim: j i=> [|j ih] i S T x hij hS hT hx hy.
- have hi : i = 0%N by apply/eqP; move: hij; rewrite leqn0.
  subst i; have -> := @partition_cells_meeting_equal X (P 0%N) T S x
    (refining_partition_levels hp 0%N) hT hS hy hx.
  exact: subset_refl.
- move: hij; rewrite leq_eqVlt=> /orP [/eqP he|hij].
  + subst i; have -> := @partition_cells_meeting_equal X (P j.+1) T S x
      (refining_partition_levels hp j.+1) hT hS hy hx.
    exact: subset_refl.
  + rewrite ltnS in hij.
    have [U [hU hxU]] := @partition_level_point_cell X P hp j x.
    have hTU := @partition_successor_meeting_subset X P hp j U T x hU hT hxU hy.
    have hUS := ih i S U x hij hS hU hx hxU.
    exact: subset_trans hTU hUS.
Qed.

(** Source for [partition_levels_countable]: countability
    of the union of all level families in Federer 2.8.19,
    p. 152, from countable Borel partitions. This fact
    supplies countability of its maximal subfamily. *)
Lemma partition_levels_countable (X : topologicalType) (P : nat -> set (set X)) :
  is_refining_borel_partitions P -> countable (partition_levels_family P).
Proof.
move=> hp; apply: bigcup_countable; first exact: countableP.
move=> n _; exact: borel_partition_countable (refining_partition_levels hp n).
Qed.
