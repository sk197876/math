(** Federer (1969), 2.5.14, pp. 107–108: a countably subadditive cost on
    open sets extends to a measure by taking an outer infimum. We use
    arbitrary countable families, as in Federer's measure definition 2.1.2,
    rather than a fixed sequence enumeration. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_open_cover_content]: supporting abstract hypotheses for
    the measure construction in Federer 2.5.14, pp. 107–108 The values
    outside the open sets have no mathematical significance. *)
Record is_open_cover_content (R : realType) (X : topologicalType)
    (a : set X -> \bar R) : Prop := {
  (** Source for [open_cover_content_nonnegative]: Supporting Federer 2.5.14,
    p. 107. *)
  open_cover_content_nonnegative : forall V, open V -> 0 <= a V;
  (** Source for [open_cover_content_empty]: alpha(empty)=0, supporting
    Federer 2.5.14, p. 108 *)
  open_cover_content_empty : a set0=0;
  (** Source for [open_cover_content_cover]: countable open-cover bound in
    Federer 2.5.14, pp. 107–108, formulated with containment. *)
  open_cover_content_cover : forall W C, open W -> countable C ->
    (forall V, C V -> open V) -> W `<=` \bigcup_(V in C) V ->
    a W <= nonnegative_sum C a
}.

(** Source for [is_open_cover_envelope]: abstract infimum specification of
    Phi(A) in Federer 2.5.14, p. 107 Existence and measure laws are separate
    theorems, not assumed project axioms. *)
Record is_open_cover_envelope (R : realType) (X : topologicalType)
    (a nu : set X -> \bar R) : Prop := {
  (** Source for [open_cover_envelope_lower]: every open
      superset bounds the infimum in Federer 2.5.14, p. 107. *)
  open_cover_envelope_lower : forall S V, open V -> S `<=` V -> nu S <= a V;
  (** Source for [open_cover_envelope_greatest]: greatestness
      of the displayed infimum in Federer 2.5.14, p. 107. *)
  open_cover_envelope_greatest : forall S b,
    (forall V, open V -> S `<=` V -> b <= a V) -> b <= nu S
}.
