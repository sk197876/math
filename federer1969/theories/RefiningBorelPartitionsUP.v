(** Federer (1969), 2.8.19, p. 152: refining Borel partitions with uniformly
    shrinking diameters. the numbered theorem will retain the printed
    Federer hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import BorelPartition MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_refining_borel_partitions]: the Borel
    partition and refinement hypotheses of Federer 2.8.19,
    p. 152. Formal level zero is printed level one.
    The refinement is stated by exactly the printed union law. *)
Record is_refining_borel_partitions (X : topologicalType) (P : nat -> set (set X)) : Prop := {
  (** Source for [refining_partition_levels]: each level is
      a Borel partition of X, Federer 2.8.19, p. 152;
      countability is part of 2.2.1, p. 60. *)
  refining_partition_levels : forall n, is_borel_partition setT (P n);
  (** Source for [refining_partition_successor]: every member
      of a level is a union of members of the next level,
      Federer 2.8.19, p. 152. *)
  refining_partition_successor : forall n S, P n S ->
    exists H : set (set X), H `<=` P n.+1 /\ (\bigcup_(T in H) T) = S
}.

(** Source for [partition_levels_family]: the family of all partition cells
    implicit in the relation of Federer 2.8.19, p. 152 *)
Definition partition_levels_family (X : Type) (P : nat -> set (set X)) :=
  \bigcup_(n in @setT nat) P n.

(** Source for [partition_level_diameter_sup]: the supremum
    inside the displayed diameter limit in Federer 2.8.19,
    p. 152. Diameters and suprema use their sealed laws. *)
Definition partition_level_diameter_sup (R : realType) (X : metricType R)
    (P : nat -> set (set X)) n := extended_real_sup ((@extended_metric_diameter R X) @` P n).

(** Source for [partition_covering_relation]: the displayed
    V in Federer 2.8.19, p. 152: x in S in
    some partition level. It retains the base point explicitly. *)
Definition partition_covering_relation (X : Type) (P : nat -> set (set X)) :=
  fun (x : X) (S : set X) => S x /\ partition_levels_family P S.

(** Source for [is_maximal_family_member]: the maximal
    members of C(Z) in the proof of Federer 2.8.19,
    p. 152. Maximal means maximal for inclusion, with
    equality expressed by two inclusions. Empty members are
    not excluded from this auxiliary definition. *)
Definition is_maximal_family_member (X : Type) (F : set (set X)) (S : set X) :=
  F S /\ forall T, F T -> S `<=` T -> T `<=` S.
