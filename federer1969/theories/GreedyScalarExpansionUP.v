(** Federer (1969), 2.3.3, p. 76: scalar form of the greedy partial-sum
    recursion. Source and erratum details:
    WeightedCharacteristicExpansionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [is_greedy_scalar_expansion]: abstract partial-sum
    recurrence from the set recursion in Federer 2.3.3, p. 76.
    The next positive weight is included exactly when the enlarged
    partial sum does not exceed the target. Indices start at zero. *)
Record is_greedy_scalar_expansion (R : realType) (r : nat -> R) (t : \bar R)
    (s : nat -> R) : Prop := {
  (** Source for [greedy_scalar_initial]: empty partial sum in
      the induction of Federer 2.3.3, p. 76. *)
  greedy_scalar_initial : s 0%N = 0%R;
  (** Source for [greedy_scalar_step]: the include-or-omit step
      of the induction in Federer 2.3.3, p. 76. *)
  greedy_scalar_step : forall n,
    s n.+1 = if (s n + r n)%R%:E <= t then (s n + r n)%R else s n
}.

(** Source for [greedy_scalar_term]: supporting selected weighted
    summand in the representation of Federer 2.3.3, p. 76. *)
Definition greedy_scalar_term (R : realType) (r : nat -> R) (t : \bar R)
    (s : nat -> R) n := if (s n + r n)%R%:E <= t then r n else 0%R.
