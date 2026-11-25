(** Federer (1969), 2.3.2, p. 73: measurable functions with conull, possibly
    proper domains and topological targets. The source type is the measured
    space X; values of a set-theoretic function outside X are irrelevant and
    are represented by restricting its graph to X. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_measure_measurable_function]: direct first
    definition of Federer 2.3.2, p. 73. The target membership
    condition is carried by the graph's value type; conull domain
    and measurability of open inverse images are separate laws. *)
Record is_measure_measurable_function (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (f : partial_function X Y) : Prop := {
  (** Source for [measurable_function_domain]: the conull-domain
      clause in Federer 2.3.2, p. 73, first sentence. *)
  measurable_function_domain : measure_almost_everywhere mu (partial_function_domain f);
  (** Source for [measurable_function_open_preimage]: the open
      inverse-image clause in Federer 2.3.2, p. 73, first sentence. *)
  measurable_function_open_preimage : forall U, open U ->
    measure_measurable mu (partial_function_preimage f U)
}.
