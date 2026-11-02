(** Set-theoretic support for Federer (1969), 2.4.8, p. 84: a countable
    indexing set admits an increasing exhaustion by finite subsets. This
    reduces the countable family to the sequence theorem 2.4.7. The abstract
    exhaustion laws below support Federer's more general countable-index
    formulation. *)
From mathcomp Require Import all_boot finmap classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [is_countable_finite_exhaustion]: supporting
    abstract finite-exhaustion laws for the indexing set in
    Federer 2.4.8, p. 84. *)
Record is_countable_finite_exhaustion (J : choiceType) (D : set J)
    (C : nat -> {fset J}) : Prop := {
  (** Source for [finite_exhaustion_initial]: empty initial sum
      supporting Federer 2.4.8, p. 84. *)
  finite_exhaustion_initial : C 0%N = fset0;
  (** Source for [finite_exhaustion_subset]: each finite set lies
      in the indexing set of Federer 2.4.8, p. 84. *)
  finite_exhaustion_subset : forall n j, j \in C n -> D j;
  (** Source for [finite_exhaustion_increasing]: increasing finite
      partial sums supporting Federer 2.4.8, p. 84. *)
  finite_exhaustion_increasing : forall n m, (n <= m)%N -> (C n `<=` C m)%fset;
  (** Source for [finite_exhaustion_cover]: every index eventually
      occurs, supporting the full sum in Federer 2.4.8, p. 84. *)
  finite_exhaustion_cover : forall j, D j -> exists n, j \in C n
}.
