(** Federer (1969), 2.5.20, p. 114: E=K(Y), with the uniform norm, is the
    vector space used for disintegration. This specification describes the
    function space through its evaluations and its bijection with K(Y). A
    concrete subtype supplies existence separately. The norm is the supremum
    norm already specified for 2.5.19, p. 113. The local erratum has no
    entry for book p. 114. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_function_space]: abstract realization
    of E=K(Y) in Federer 2.5.20, p. 114. Evaluation
    preserves vector operations, separates vectors, and represents
    precisely the compactly supported continuous scalar functions. *)
Record is_compact_function_space (R : realType) (Y : topologicalType)
    (V : lmodType R) (ev : V -> Y -> R) : Prop := {
  (** Source for [compact_function_evaluation_linear]: pointwise
      vector operations on K(Y), Federer 2.5.20, p. 114. *)
  compact_function_evaluation_linear : forall c u v y, ev (c*:u+v) y=c*ev u y+ev v y;
  (** Source for [compact_function_evaluation_member]: evaluations
      yield members of K(Y), Federer 2.5.20, p. 114. *)
  compact_function_evaluation_member : forall v, compactly_supported_continuous_functions (ev v);
  (** Source for [compact_function_evaluation_injective]: actual
      functions identify the vectors of K(Y), Federer 2.5.20, p. 114. *)
  compact_function_evaluation_injective : injective ev;
  (** Source for [compact_function_evaluation_surjective]: every
      member of K(Y) has a representative vector, Federer 2.5.20, p. 114. *)
  compact_function_evaluation_surjective : forall f, compactly_supported_continuous_functions f -> exists v, ev v=f
}.
