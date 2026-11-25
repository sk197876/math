(** Federer (1969), 2.5.13, p. 106: choose a nonnegative continuous
    compactly supported function equal to one on the compact support of g.
    The same cutoff for an arbitrary compact K is used in 2.5.14, p. 107. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_cutoff]: abstract specification of
    the cutoff in Federer 2.5.13, p. 106. The optional
    upper bound one is included, as permitted by truncation of the
    printed nonnegative cutoff. No implementation is part of these laws. *)
Record is_compact_cutoff (R : realType) (X : topologicalType) (K : set X) (f : X -> R) : Prop := {
  (** Source for [compact_cutoff_function]: continuous compact
      support in the cutoff used in Federer 2.5.13, p. 106. *)
  compact_cutoff_function : compactly_supported_continuous_functions f;
  (** Source for [compact_cutoff_range]: nonnegativity in Federer
      2.5.13, p. 106; truncate at one to obtain the upper bound. *)
  compact_cutoff_range : forall x, 0 <= f x <= 1;
  (** Source for [compact_cutoff_on_set]: equality to one on
      the compact set in Federer 2.5.13, p. 106. *)
  compact_cutoff_on_set : forall x, K x -> f x= 1
}.
