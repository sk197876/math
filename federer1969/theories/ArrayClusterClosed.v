(** General topology supporting Federer (1969), 2.10.22, pp. 184–185:
    compact flagged factors and closed coordinate constraints at a cluster
    row. This makes inactive cover positions explicit without inserting the
    empty set into F. Source context and Kelley reference:
    CompactArrayCluster.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality topology.
From Federer Require Import ArrayClusterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [array_cluster_closed_coordinate]: supporting
    preservation of a closed generator constraint in
    2.10.22, pp. 184–185. A constraint
    need hold only in sufficiently late source rows. *)
Theorem array_cluster_closed_coordinate (Y : topologicalType)
    (u : nat -> nat -> Y) (v : nat -> Y) (C : set Y) (N k : nat) :
  is_countable_array_cluster u v -> closed C ->
  (forall j, (N<=j)%N -> C (u j k)) -> C (v k).
Proof.
move=> hcluster hC hu; apply: hC=> V hV.
pose W n := if n==k then V else setT.
have hW n : n \in [fset k] -> nbhs (v n) (W n).
  move=> /fset1P ->; by rewrite /W eqxx.
have [j [hNj hj]] := hcluster N [fset k] W hW.
exists (u j k); split; first exact: hu j hNj.
have hh := hj k (fset11 k); by rewrite /W eqxx in hh.
Qed.

(** Source for [flagged_closed_condition]: supporting
    closed diameter constraint for active positions
    in 2.10.22, pp. 184–185. Inactive
    positions impose no condition on their stored datum. *)
Theorem flagged_closed_condition (Y : topologicalType) (C : set Y) :
  closed C -> closed [set p : bool*Y | p.1 -> C p.2].
Proof.
move=> hC; have ho : open (~` [set p : bool*Y | p.1 -> C p.2]).
  rewrite openE; move=> [b y] hy; case: b hy=> hy.
  - have hnot : ~C y by move=> hCy; apply: hy; move=> _; exact hCy.
    have hO := closed_openC hC; rewrite openE in hO.
    exists ([set true], ~` C).
    + split; [exact: discrete_set1|exact: hO y hnot].
    + move=> [b z] [hb hz] hgood.
      have he : b=true := hb; apply: hz; apply: hgood; by rewrite he.
  - exfalso; apply: hy; by move=> hfalse.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [compact_flagged_family]: supporting
    compact factor for finite/countable compact covers
    in 2.10.22, pp. 184–185. Both
    Boolean flags are retained, including inactive positions. *)
Theorem compact_flagged_family (Y : topologicalType) (K : set Y) :
  compact K -> compact [set p : bool*Y | K p.2].
Proof.
move=> hK.
have he : [set p : bool*Y | K p.2]=setT `*` K.
  by apply/seteqP; split=> [[b y] hy|[b y] [_ hy]]; [split|].
rewrite he; apply: compact_setX.
- apply: finite_compact; exact: finite_finset.
- exact hK.
Qed.
