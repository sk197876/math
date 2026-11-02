(** Federer (1969), 2.4.9, p. 85, displayed chain after Fatou: a nonnegative
    error has limit zero when liminf of its complement is at least the fixed
    total. This supporting reformulation uses strict eventual lower bounds
    instead of introducing a second scalar limsup getter. It is equivalent
    to the book's limsup calculation. Source context:
    MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedLowerLimit
  ExtendedConvergentLowerLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [fatou_reflected_nonnegative_error_limit]: supporting
    scalar consequence of the displayed Fatou inequality in
    Federer 2.4.9, p. 85. The fixed integral c is
    finite because the dominating function is summable. *)
Lemma fatou_reflected_nonnegative_error_limit (R : realType) (e : nat -> R) (c : R) :
  (forall n, (0 <= e n)%R) ->
  c%:E <= extended_lower_limit (fun n => (c-e n)%:E) ->
  extended_order_limit (fun n => (e n)%:E) 0.
Proof.
move=> hp hlim; apply: real_error_extended_order_limit=> r hr.
have hstrict : (c-r)%:E < extended_lower_limit (fun n => (c-e n)%:E).
  apply: lt_le_trans _ hlim; by rewrite lte_fin ltrBlDr ltrDl.
have [N hN] := @extended_lower_limit_strict_eventual R (fun n => (c-e n)%:E) _ _
  (extended_lower_limit_laws _) hstrict.
exists N=> n hn; rewrite subr0 (ger0_norm (hp n)).
by move: (hN n hn); rewrite lte_fin ltrD2l ltrN2.
Qed.
