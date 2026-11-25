(** Federer (1969), 2.5.14, pp. 107–108: the compactly supported test
    functions can be localized in an open neighborhood of a compact set.
    This general-topology step supplies the measurable open base and finite
    partition of unity. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_localized_compact_cutoff]: supporting laws for the
    localized functions in Federer 2.5.14, pp. 107–108 The support, not
    merely the nonzero locus, must lie in the prescribed open set. *)
Record is_localized_compact_cutoff (R : realType) (X : topologicalType)
    (K V : set X) (f : X -> R) : Prop := {
  (** Source for [localized_compact_cutoff_laws]: compact support,
      range [0,1], and equality to one on K, supporting Federer
      2.5.14, p. 108, partition of unity. *)
  localized_compact_cutoff_laws : is_compact_cutoff K f;
  (** Source for [localized_compact_cutoff_support]: support
      contained in V, as required in Federer 2.5.14, p. 108. *)
  localized_compact_cutoff_support : real_function_support f `<=` V
}.
