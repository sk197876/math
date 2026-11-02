(** Federer (1969), 2.10.22, pp. 184–185: supporting cost-ordered
    representation of near-optimal countable covers. Genuine selected
    generators occur once, all positive costs occur, and position n has cost
    at most M/(n+1). Inactive positions have zero cost without pretending an
    empty set belongs to the compact generator family. The selection is
    specified before its existence construction. Source context and
    proof-route explanation: SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [optional_generator_cost]: supporting
    inactive-slot convention for finite covers in
    2.10.22, pp. 184–185. None contributes zero;
    Some retains the original generator cost. *)
Definition optional_generator_cost (R : realType) (I : Type) (w : I -> R) (o : option I) :=
  if o is Some x then w x else 0.

(** Source for [is_summable_cost_enumeration]: abstract
    cover-selection laws supporting 2.10.22,
    pp. 184–185. Only positive-cost generators are
    selected; zero-cost generators will be removed
    through their proved nullity. *)
Record is_summable_cost_enumeration (R : realType) (I : choiceType)
    (G : set I) (w : I -> R) (M : R) (u : nat -> option I) : Prop := {
  (** Source for [cost_enumeration_member_law]: selected
      positive-cost members of the source cover,
      2.10.22, p. 184. *)
  cost_enumeration_member_law : forall n x, u n=Some x -> G x /\ 0<w x;
  (** Source for [cost_enumeration_injective_law]: supporting
      preservation of covering cost without repetitions,
      2.10.22, pp. 184–185. *)
  cost_enumeration_injective_law : forall n m x, u n=Some x -> u m=Some x -> n=m;
  (** Source for [cost_enumeration_covers_positive_law]: supporting
      enumeration of every positive-cost generator,
      2.10.22, p. 184. *)
  cost_enumeration_covers_positive_law : forall x, G x -> 0<w x -> exists n, u n=Some x;
  (** Source for [cost_enumeration_uniform_bound_law]: supporting
      uniform smallness of late costs in 2.10.22,
      p. 185. The natural position n denotes the
      book's positive position n+1. *)
  cost_enumeration_uniform_bound_law : forall n,
    n.+1%:R*optional_generator_cost w (u n)<=M
}.
