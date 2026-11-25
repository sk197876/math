(** Finite disjoint rectangle partitions for the Bohr packing
    supporting Federer (1969), 2.8.20, p. 152;
    Saks1934 Lemma B, p. 258, and Cesari1939
    Lemma III, p. 306. The predicate isolates the
    laws used while repeatedly filling the remaining regions.
    Empty cells are discarded and an empty family partitions
    the empty remainder. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import CountablyClosedFamilyUP ScalarHalfOpenRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_finite_half_open_partition]: supporting
    specification of the finite remaining rectangular pieces
    for Federer 2.8.20, p. 152. It asserts
    finiteness, positive half-open rectangles, disjointness
    and exact union, without choosing any decomposition. *)
Record is_finite_half_open_partition (R : realType) (A : set (R*R))
    (G : set (set (R*R))) : Prop := {
  (** Source for [half_open_partition_finite]: finite region
      family in the construction supporting Federer 2.8.20,
      p. 152; Saks1934 Lemma B, p. 258. *)
  half_open_partition_finite : finite_set G;
  (** Source for [half_open_partition_rectangles]: nonempty
      half-open coordinate pieces used only as auxiliary
      regions for Federer 2.8.20, p. 152. *)
  half_open_partition_rectangles : forall S, G S -> is_nondegenerate_half_open_rectangle S;
  (** Source for [half_open_partition_disjoint]: pairwise
      disjoint remaining regions in the construction supporting
      Federer 2.8.20, p. 152. *)
  half_open_partition_disjoint : set_family_disjoint G;
  (** Source for [half_open_partition_union]: exact remaining
      region covered by the partition for the construction
      supporting Federer 2.8.20, p. 152. *)
  half_open_partition_union : (\bigcup_(S in G) S) = A
}.

(** Source for [half_open_partition_member_subset]: supporting
    containment of each selected region in its remainder for
    Federer 2.8.20, p. 152. Only the abstract
    union law is used. *)
Lemma half_open_partition_member_subset (R : realType) (A : set (R*R))
    (G : set (set (R*R))) :
  is_finite_half_open_partition A G -> forall S, G S -> S `<=` A.
Proof.
move=> h S hS x hx; rewrite -(half_open_partition_union h); by exists S.
Qed.
