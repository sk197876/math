(** Federer (1969), proof of 2.4.4(2), p. 83: the disjoint intervals
    [t^j,t^(j+1)), j an integer, cover the positive real axis when t>1.
    Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GeometricPowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_natural_cell]: supporting first-
    crossing argument for positive values at least one in the
    geometric partition of Federer 2.4.4(2), p. 83. *)
Lemma geometric_natural_cell (R : realType) (t x : R) :
  1 < t -> 1 <= x -> exists n : nat, t^+n <= x /\ x < t^+n.+1.
Proof.
move=> ht hx; have hex := @geometric_powers_unbounded R t x ht.
have [k hk hmin] := ex_minnP hex.
case: k hk hmin=> [|n] hk hmin.
- by move: hk; rewrite expr0 ltNge hx.
- exists n; split=> //; rewrite leNgt; apply/negP=> hn.
  have hh := hmin n hn; by move: hh; rewrite leqNgt ltnSn.
Qed.

(** Source for [geometric_integer_cell_exists]: complete coverage
    by the integer cells in Federer 2.4.4(2), p. 83.
    A finite power rescaling reduces small positive values to
    the preceding natural first-crossing argument. *)
Lemma geometric_integer_cell_exists (R : realType) (t x : R) :
  1 < t -> 0 < x -> exists j : int, t^j <= x /\ x < t^(j+1).
Proof.
move=> ht hx; have ht0 : 0 < t := lt_trans ltr01 ht.
have htN : t != 0 by rewrite gt_eqF.
have [m hm] := @geometric_powers_unbounded R t x^-1 ht.
have hm0 : 0 < t^+m := exprn_gt0 _ ht0.
have hlarge : 1 <= x*t^+m.
  apply: ltW; rewrite -ltr_pdivrMl // mulr1; exact hm.
have [n [hn hnext]] := @geometric_natural_cell R t (x*t^+m) ht hlarge.
exists (n%:Z-m%:Z).
have he : t^(n%:Z-m%:Z) = t^+n / t^+m.
  by rewrite expfzDr // -invr_expz -!exprnP.
split.
- by rewrite he ler_pdivrMr.
- rewrite expfzDr // expr1z he mulrAC ltr_pdivlMr // -exprSr.
  exact hnext.
Qed.

(** Source for [geometric_integer_cell_unique]: disjointness
    of the geometric cells in Federer 2.4.4(2), p. 83.
    Endpoint conventions are exactly closed below and open above. *)
Lemma geometric_integer_cell_unique (R : realType) (t x : R) (i j : int) :
  1 < t -> t^i <= x -> x < t^(i+1) -> t^j <= x -> x < t^(j+1) -> i=j.
Proof.
move=> ht hil hiu hjl hju; apply/eqP; rewrite eq_le; apply/andP; split.
- have h : t^i < t^(j+1) := le_lt_trans hil hju.
  by move: h; rewrite ltr_eXz2l // ltzD1.
- have h : t^j < t^(i+1) := le_lt_trans hjl hiu.
  by move: h; rewrite ltr_eXz2l // ltzD1.
Qed.
