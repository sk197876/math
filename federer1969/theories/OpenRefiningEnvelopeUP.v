(** Federer (1969), 2.10.1, p. 170, alternative construction: fix an open
    cover and restrict generators to its refinements. This supporting
    infimum is specified by its order laws before constructing a witness.
    The corrected paper reference is Federer1955 Theorem 2.5, pp. 291–292
    (local erratum p. 3, book p. 170 lines 24 and 35). The
    arbitrary-topological extension below uses covers of the whole space;
    the literal A-cover extension is refuted in
    OpenRefinementNonmonotonicity.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [generator_refines_cover]: direct containment
    requirement on a generator in Federer 2.10.1, p. 170:
    it is contained in some member of the given open cover.
    The relation itself needs no topology or openness hypothesis. *)
Definition generator_refines_cover (X J : Type) (S : J -> set X)
    (H : set (set X)) (j : J) := exists U, H U /\ S j `<=` U.

(** Source for [is_open_refining_envelope]: supporting fixed-cover
    infimum in the alternative construction of Federer 2.10.1,
    p. 170. The lower and greatest clauses specify exactly
    countable generator covers refining H. Openness and the
    whole-space covering condition are imposed separately when
    taking the final supremum; no project axiom is introduced. *)
Record is_open_refining_envelope (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X))
    (nu : set X -> \bar R) : Prop := {
  (** Source for [open_refining_envelope_lower]: each admissible
      refined cover bounds the infimum supporting Federer
      2.10.1, p. 170. *)
  open_refining_envelope_lower : forall A G, countable G ->
    (forall j, G j -> generator_refines_cover S H j) ->
    A `<=` \bigcup_(j in G) S j -> nu A<=nonnegative_sum G cost;
  (** Source for [open_refining_envelope_greatest]: greatest
      lower-bound clause for the fixed-open-cover infimum
      supporting Federer 2.10.1, p. 170. *)
  open_refining_envelope_greatest : forall A b,
    (forall G, countable G -> (forall j, G j -> generator_refines_cover S H j) ->
      A `<=` \bigcup_(j in G) S j -> b<=nonnegative_sum G cost) -> b<=nu A
}.
