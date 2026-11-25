(** Federer (1969), proof of 2.4.4(2), p. 83: integer geometric cells cover
    all positive finite values. This file supplies the elementary
    unboundedness of powers for a real base greater than one. The elementary
    induction is supporting infrastructure, not a separately numbered
    assertion in either source. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_power_linear_lower_bound]: elementary
    induction supporting the geometric cell coverage in Federer
    2.4.4(2), p. 83. *)
Lemma geometric_power_linear_lower_bound (R : realType) (t : R) n :
  1 <= t -> 1+n%:R*(t-1) <= t^+n.
Proof.
move=> ht; have ht0 : 0 <= t := le_trans ler01 ht.
have hd : 0 <= t-1 by rewrite subr_ge0.
elim: n=> [|n ih]; first by rewrite expr0 mul0r addr0.
have he : 1+(n.+1)%:R*(t-1) = t+n%:R*(t-1).
  have he1 : 1+(t-1) = t by rewrite addrCA subrr addr0.
  by rewrite -addn1 natrD mulrDl mul1r addrCA he1 addrC.
rewrite he exprS.
have hmul : t*(1+n%:R*(t-1)) <= t*t^+n.
  rewrite ler_pM2l //; exact: lt_le_trans ltr01 ht.
apply: le_trans _ hmul.
rewrite [t * (1 + _)]mulrDr mulr1 lerD2l.
apply: ler_peMl=> //; exact: mulr_ge0 (ler0n _ _) hd.
Qed.

(** Source for [geometric_powers_unbounded]: elementary real
    Archimedean consequence supporting the cells in Federer
    2.4.4(2), p. 83, without importing logarithms. *)
Lemma geometric_powers_unbounded (R : realType) (t x : R) :
  1 < t -> exists n : nat, x < t^+n.
Proof.
move=> ht; have hd : 0 < t-1 by rewrite subr_gt0.
pose y := Order.max x 0.
have hy : 0 <= y by rewrite /y le_max lexx orbT.
pose n := Num.bound (y/(t-1)).
have hn : y/(t-1) < n%:R by apply: archi_boundP; exact: divr_ge0 hy (ltW hd).
have hyn : y < n%:R*(t-1) by rewrite -ltr_pdivrMr.
have hxy : x <= y by rewrite /y le_max lexx.
exists n; apply: lt_le_trans (le_lt_trans hxy hyn) _.
apply: le_trans _ (@geometric_power_linear_lower_bound R t n (ltW ht)).
by rewrite lerDr ler01.
Qed.
