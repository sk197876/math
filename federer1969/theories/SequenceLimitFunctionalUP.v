(** Federer (1969), 2.5.3, p. 95, final display: lambda sends a convergent
    sequence to its limit. The abstract specification records the limit law
    on L; off-L values of an ambient representative are irrelevant. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ConvergentSequenceLattice ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_sequence_limit_functional]: direct abstract
    limit-functional definition in Federer 2.5.3, p. 95 *)
Definition is_sequence_limit_functional (R : realType) (A : (nat -> R) -> R) :=
  forall f, convergent_real_sequences f -> extended_order_limit (fun n => (f n)%:E) (A f)%:E.

(** Source for [sequence_limit_functional_value]: uniqueness of the assigned
    limit in Federer 2.5.3, p. 95 *)
Lemma sequence_limit_functional_value (R : realType) (A : (nat -> R) -> R)
    (hA : is_sequence_limit_functional A) (f : nat -> R) (a : R) :
  extended_order_limit (fun n => (f n)%:E) a%:E -> A f=a.
Proof.
move=> hf; have hmem : convergent_real_sequences f by exists a.
have he := extended_order_limit_unique (hA f hmem) hf; by injection he.
Qed.
