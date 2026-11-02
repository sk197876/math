(** Federer (1969), 2.1.5(1), p. 57: comparison of the limiting measure with
    the measure of the union. Supporting order-limit facts for the printed
    inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit_upper_bound]: Federer
    2.1.5(1), p. 57, supporting passage of a constant upper bound
    to an extended-real limit; this includes either infinite endpoint. *)
Lemma extended_order_limit_upper_bound (R : realType) (u : nat -> \bar R) l b :
  extended_order_limit u l -> (forall n, u n <= b) -> l <= b.
Proof.
move=> [hl _] hb; rewrite leNgt; apply/negP=> hbl.
have [N hN] := hl b hbl; have h := hN N (leqnn N).
by move: h; rewrite ltNge (hb N).
Qed.

(** Source for [extended_order_limit_lower_bound]: Federer
    2.1.5(1), p. 57, supporting dual constant-bound rule for limits. *)
Lemma extended_order_limit_lower_bound (R : realType) (u : nat -> \bar R) l a :
  extended_order_limit u l -> (forall n, a <= u n) -> a <= l.
Proof.
move=> [_ hu] ha; rewrite leNgt; apply/negP=> hla.
have [N hN] := hu a hla; have h := hN N (leqnn N).
by move: h; rewrite ltNge (ha N).
Qed.
