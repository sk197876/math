(** Federer (1969), 2.5.14, p. 108, first display: a finite partition of
    unity on the compact support of f, subordinate to its open cover. Finite
    sets index the selected original cover members, preventing repeated
    costs in later estimates. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_compact_partition]: abstract specification of the
    g_n in Federer 2.5.14, p. 108 Equality to one is required on K, not on
    the whole ambient space. *)
Record is_finite_compact_partition (R : realType) (X : topologicalType) (J : choiceType)
    (V : J -> set X) (F : {fset J}) (K : set X) (g : J -> X -> R) : Prop := {
  (** Source for [finite_compact_partition_functions]: the g_n
      belong to K(X) in Federer 2.5.14, p. 108. *)
  finite_compact_partition_functions : forall j, j \in F -> compactly_supported_continuous_functions (g j);
  (** Source for [finite_compact_partition_range]: 0 <= g_n <= 1
      in Federer 2.5.14, p. 108. *)
  finite_compact_partition_range : forall j, j \in F -> forall x, 0 <= g j x <= 1;
  (** Source for [finite_compact_partition_support]: support g_n
      lies in the assigned open set in Federer 2.5.14, p. 108. *)
  finite_compact_partition_support : forall j, j \in F -> real_function_support (g j) `<=` V j;
  (** Source for [finite_compact_partition_sum]: the sum of g_n
      is one on K, as displayed in Federer 2.5.14, p. 108. *)
  finite_compact_partition_sum : forall x, K x -> \sum_(j <- F) g j x= 1
}.
