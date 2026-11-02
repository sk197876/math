(** Federer (1969), 2.5.20, p. 114: the conjugate of E=K(Y) is the space of
    Daniell integrals on K(Y), as established in 2.5.19, p. 113. This
    abstract identification includes weak continuity, needed to transfer the
    measurability supplied by 2.5.12. Source context and the absence of a
    matching. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP CompactSupportFunctionUP
  VectorDaniellHypotheses DaniellIntegralUP DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_function_dual_identification]:
    specification of the identification of E* with Daniell
    integrals used in Federer 2.5.20, p. 114, with
    the weak topologies of 2.5.12(2), p. 103,
    and 2.5.19, p. 113. Values outside K(Y) are
    immaterial and are not constrained. *)
Record is_compact_function_dual_identification (R : realType)
    (Y : topologicalType) (E : lmodType R) (N : E -> R)
    (hN : is_real_norm N) (ev : E -> Y -> R)
    (F : weak_dual_space hN -> daniell_weak_space
      (@compactly_supported_continuous_functions R Y)) : Prop := {
  (** Source for [compact_function_dual_evaluation]: preservation
      of the pairing in Federer 2.5.20, p. 114. *)
  compact_function_dual_evaluation : forall a v, F a (ev v)=val a v;
  (** Source for [compact_function_dual_daniell]: the resulting
      functional is a Daniell integral, Federer 2.5.20,
      p. 114, by 2.5.19, p. 113. *)
  compact_function_dual_daniell : forall a,
    is_daniell_integral (@compactly_supported_continuous_functions R Y) (F a);
  (** Source for [compact_function_dual_continuous]: the
      identification preserves the weak topology, supporting
      the measurability assertion in Federer 2.5.20, p. 114. *)
  compact_function_dual_continuous : continuous F
}.
