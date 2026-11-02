(** Federer (1969), 2.1.1(3), p. 52, applied to the infinite characteristic
    weight in 2.6.2(2), pp. 115–116. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumConstant NonnegativeSumExtendedScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_series_constant]: supporting numerical
    identity for the rectangle calculation in Federer 2.6.2,
    p. 116: the series of a nonnegative extended constant is
    infinity times that constant, including the zero case.
    This follows from the numerical sum of 2.1.1(3), p. 52. *)
Lemma nonnegative_series_constant (R : realType) (c : \bar R) :
  0 <= c -> nonnegative_sum setT (fun _ : nat => c) = +oo*c.
Proof.
move=> hc.
have he : (fun _ : nat => c) = (fun _ : nat => c*1) by apply: funext=> n; rewrite mule1.
have h1 : forall n : nat, setT n -> (0 : \bar R) <= 1 by move=> n _; exact: lee01.
rewrite he (nonnegative_sum_extended_scale hc h1).
rewrite (@nonnegative_sum_infinite_constant R [the choiceType of (nat : Type)] setT 1%R (@ltr01 R) infinite_nat).
exact: muleC.
Qed.
