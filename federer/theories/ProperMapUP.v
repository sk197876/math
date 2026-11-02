(** Federer (1969), 2.2.17, p. 72: proper continuous maps of locally compact
    Hausdorff spaces, with a countable compact cover of the source. *)
From mathcomp Require Import all_boot classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_proper_map]: direct parenthetical definition
    in Federer 2.2.17, p. 72: inverse images
    of compact subsets are compact. Continuity is a separate
    hypothesis, as in the printed statement. *)
Definition is_proper_map (X Y : topologicalType) (f : X -> Y) : Prop :=
  forall K : set Y, compact K -> compact (f @^-1` K).

(** Source for [has_countable_compact_cover]: direct source
    hypothesis in Federer 2.2.17, p. 72. The
    space is the union of a countable family of compact
    sets; the empty family is permitted for an empty space. *)
Definition has_countable_compact_cover (X : topologicalType) : Prop :=
  exists G : set (set X), countable G /\
    (forall K, G K -> compact K) /\ (\bigcup_(K in G) K) = setT.
