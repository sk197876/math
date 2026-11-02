(** The bounded Borel partition used at the end of the proof of Federer
    (1969), 2.9.2, p. 153. Here bounded pieces retain the book's original
    class M and make both measures finite. Source context:
    MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import CoveringFamilyUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_borel_partition]: abstract
    specification of the bounded disjoint Borel decomposition
    of X used in Federer 2.9.2, p. 153.
    Empty cells and an empty ambient space are allowed. *)
Record is_bounded_borel_partition (R : realType) (X : metricType R)
    (P : nat -> set X) : Prop := {
  (** Source for [bounded_borel_partition_borel]: Borel
      cells in the supporting partition for Federer 2.9.2,
      p. 153. *)
  bounded_borel_partition_borel : forall n, borel_set (P n);
  (** Source for [bounded_borel_partition_bounded]: bounded
      cells in the supporting partition for Federer 2.9.2,
      p. 153. *)
  bounded_borel_partition_bounded : forall n, metric_set_bounded (P n);
  (** Source for [bounded_borel_partition_union]: exact
      coverage of X in the partition used in Federer
      2.9.2, p. 153. *)
  bounded_borel_partition_union : (\bigcup_n P n)=setT;
  (** Source for [bounded_borel_partition_disjoint]: disjoint
      cells in the partition used in Federer 2.9.2,
      p. 153. Indices start at zero. *)
  bounded_borel_partition_disjoint : forall n m, n != m ->
    forall x, P n x -> P m x -> False
}.
