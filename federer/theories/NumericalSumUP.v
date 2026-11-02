(** Federer (1969), 2.1.1(3)-(4), p. 52: characterization of arbitrary
    numerical summation by finite nonnegative sums and subtraction of
    variations. Source context: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSumUP NonnegativeSumSealed
  NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_numerical_summation]: Federer 2.1.1(3)-(4),
    p. 52; axiomatic specification of the partial operator. On
    nonnegative functions it is the finite-subsum supremum; on
    every function it is precisely the partial difference of its
    two nonnegative sums. These are laws to prove, not project axioms. *)
Record is_numerical_summation (R : realType) (I : choiceType)
    (S : set I -> (I -> \bar R) -> option (\bar R)) : Prop := {
  numerical_summation_nonnegative : forall A f,
    (forall x, A x -> 0 <= f x) ->
    exists c, S A f = Some c /\ is_nonnegative_sum A f c;
  numerical_summation_variations : forall A f,
    S A f = match S A (fun x => extended_positive_part (f x)),
                  S A (fun x => extended_negative_part (f x)) with
      | Some p, Some n => extended_subtract p n
      | _, _ => None
      end
}.

(** Source for [numerical_summation_exists]: Federer 2.1.1, p. 52,
    construction (1)-(4); the developed operator obeys the abstract
    characterization. *)
Theorem numerical_summation_exists (R : realType) (I : choiceType) :
  is_numerical_summation (@numerical_sum R I).
Proof.
constructor.
- move=> A f hf; exists (nonnegative_sum A f); split.
  + exact: numerical_sum_nonnegative.
  + exact: NonnegativeSum.laws.
- move=> A f.
  have hp : forall x, A x -> 0 <= extended_positive_part (f x).
    by move=> x _; exact: extended_positive_part_nonnegative.
  have hn : forall x, A x -> 0 <= extended_negative_part (f x).
    by move=> x _; exact: extended_negative_part_nonnegative.
  by rewrite (numerical_sum_nonnegative hp) (numerical_sum_nonnegative hn).
Qed.

(** Source for [numerical_summation_unique]: Federer 2.1.1, p. 52,
    construction (1)-(4); the complete partial operator is uniquely
    determined, including its undefined cases. *)
Theorem numerical_summation_unique (R : realType) (I : choiceType)
    (S : set I -> (I -> \bar R) -> option (\bar R)) :
  is_numerical_summation S -> forall A f, S A f = numerical_sum A f.
Proof.
move=> hS A f; have hp : forall x, A x -> 0 <= extended_positive_part (f x).
  by move=> x _; exact: extended_positive_part_nonnegative.
have hn : forall x, A x -> 0 <= extended_negative_part (f x).
  by move=> x _; exact: extended_negative_part_nonnegative.
have [p [hps hpS]] := numerical_summation_nonnegative hS hp.
have [n [hns hnS]] := numerical_summation_nonnegative hS hn.
have ep := nonnegative_sum_unique hpS (NonnegativeSum.laws A (fun x => extended_positive_part (f x))).
have en := nonnegative_sum_unique hnS (NonnegativeSum.laws A (fun x => extended_negative_part (f x))).
by rewrite (numerical_summation_variations hS) hps hns ep en.
Qed.
