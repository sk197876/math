(** Federer (1969), 2.10.1, pp. 169–170: the preliminary measure is the
    infimum of costs of countable covers. We isolate the fixed-family part,
    independently of a metric or diameter cutoff, for the concrete
    counterexample in 2.3.8, p. 78. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_countable_cover_envelope]: abstract infimum
    specification for the fixed-family covering construction of
    Federer 2.10.1, pp. 169–170, supporting the
    2.3.8 counterexample. Indexing permits repeated generators;
    nonnegative costs make repetitions unnecessary. *)
Record is_countable_cover_envelope (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (nu : set X -> \bar R) : Prop := {
  (** Source for [countable_cover_envelope_lower]: each admissible
      covering cost bounds the infimum in Federer 2.10.1, p. 170. *)
  countable_cover_envelope_lower : forall A G, countable G ->
    A `<=` \bigcup_(j in G) S j -> nu A <= nonnegative_sum G cost;
  (** Source for [countable_cover_envelope_greatest]: greatest-lower-
      bound clause of the infimum in Federer 2.10.1, p. 170. *)
  countable_cover_envelope_greatest : forall A b,
    (forall G, countable G -> A `<=` \bigcup_(j in G) S j -> b <= nonnegative_sum G cost) -> b <= nu A
}.
