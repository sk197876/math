(** Supporting single-value computation for Federer (1969), 2.4.1, p. 80,
    from numerical summation 2.1.1(1)–(4), p. 52. It handles constant step
    functions including infinite fibre measures. Source context:
    MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum NonnegativeSumSupport NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_single_support]: supporting
    constant-step-function calculation in Federer 2.4.1, p. 80;
    all summands except one vanish, with either infinite value allowed. *)
Lemma numerical_sum_single_support (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) a :
  A a -> (forall x, A x -> x != a -> f x = 0) -> numerical_sum A f = Some (f a).
Proof.
move=> ha hz; rewrite /numerical_sum.
have hp := @nonnegative_sum_single_support R I A (fun x => extended_positive_part (f x)) a ha
  (extended_positive_part_nonnegative (f a)).
have hn := @nonnegative_sum_single_support R I A (fun x => extended_negative_part (f x)) a ha
  (extended_negative_part_nonnegative (f a)).
have hpz x (hx : A x) (hxa : x != a) : extended_positive_part (f x) = 0.
  by rewrite (hz x hx hxa) /extended_positive_part maxxx.
have hnz x (hx : A x) (hxa : x != a) : extended_negative_part (f x) = 0.
  by rewrite (hz x hx hxa) /extended_negative_part oppe0 /extended_positive_part maxxx.
by rewrite (hp hpz) (hn hnz) extended_positive_negative_parts.
Qed.
