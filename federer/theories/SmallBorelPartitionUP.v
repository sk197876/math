(** Federer (1969), 2.3.5, pp. 76–77, first step of Lusin's proof: disjoint
    countable Borel partitions of small diameter. arbitrarily small e gives
    Federer's strict diameter requirement by decreasing e. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_small_borel_partition]: abstract specification
    of the sets Y_{i,j} in Federer 2.3.5, p. 76. Empty pieces
    are allowed, including when the target space is empty. *)
Record is_small_borel_partition (R : realType) (Y : metricType R)
    (e : R) (B : nat -> set Y) : Prop := {
  (** Source for [small_partition_borel]: Borel membership in
      Federer 2.3.5, p. 76, first proof paragraph. *)
  small_partition_borel : forall n, borel_set (B n);
  (** Source for [small_partition_cover]: the union is all Y
      in Federer 2.3.5, p. 76. *)
  small_partition_cover : (\bigcup_n B n) = setT;
  (** Source for [small_partition_disjoint]: disjointness in
      Federer 2.3.5, p. 76. *)
  small_partition_disjoint : forall n m, n != m -> forall y, B n y -> B m y -> False;
  (** Source for [small_partition_diameter]: small diameters in Federer 2.3.5,
    p. 76; the supporting bound is non-strict. *)
  small_partition_diameter : forall n x y, B n x -> B n y -> mdist x y <= e
}.
