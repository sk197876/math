(** Federer (1969), 2.1.1, p. 51, fourth paragraph: decreasing extended-real
    limits. editions: ExtendedRealOrderLimit.v. These supporting order facts
    provide the dual of the increasing-limit argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit_negate]: Federer
    2.1.1, p. 51; supporting continuity of negation, which exchanges
    the two sides of every order neighborhood, including infinity. *)
Lemma extended_order_limit_negate (R : realType) (u : nat -> \bar R) l :
  extended_order_limit u l -> extended_order_limit (fun n => -u n) (-l).
Proof.
move=> [hl hu]; split.
- move=> a; rewrite lteNr => ha; have [N hN] := hu _ ha.
  exists N=> n hn; rewrite lteNr; exact: hN.
- move=> b; rewrite lteNl => hb; have [N hN] := hl _ hb.
  exists N=> n hn; rewrite lteNl; exact: hN.
Qed.

(** Source for [extended_decreasing_limit]: Federer
    2.1.1, p. 51; supporting fact: a nonincreasing sequence
    converges to the infimum of its range. *)
Lemma extended_decreasing_limit (R : realType) (u : nat -> \bar R) :
  (forall n m, (n <= m)%N -> u m <= u n) ->
  extended_decreases_to u (extended_real_inf [set t | exists n, t = u n]).
Proof.
move=> hm; split; first exact hm.
have hneg : forall n m, (n <= m)%N -> -u n <= -u m.
  move=> n m hn; rewrite leeN2; exact: hm.
have hc := extended_order_limit_negate (extended_increasing_limit hneg).2.
have he : (fun n => - -u n) = u by apply: funext=> n; exact: oppeK.
rewrite he in hc; rewrite /extended_real_inf.
have hset : [set y | [set t | exists n, t = u n] (-y)] =
    [set y | exists n, y = -u n].
  apply/seteqP; split=> y [n hn]; exists n.
  - by rewrite -hn oppeK.
  - by rewrite hn oppeK.
by rewrite hset.
Qed.
