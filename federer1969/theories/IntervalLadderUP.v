(** Federer (1969), 2.2.9, p. 65, the interval choice with countable
    complement. The scalar ladder below is local supporting infrastructure:
    two reflected ladders partition an interval, except for countably many
    endpoints, into small open intervals whose closures remain in the
    parent. It is not a separate statement in either source. Source
    editions: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_small_interval_ladder]: supporting abstract
    scalar specification for the interval refinement in Federer
    2.2.9, p. 65. A positive decreasing ladder starts at the
    half-length h, tends to zero, and has every successive gap
    smaller than the prescribed diameter e. *)
Record is_small_interval_ladder (R : realType) (h e : R) (d : nat -> R) : Prop := {
  interval_ladder_start : d 0%N = h;
  interval_ladder_positive : forall n, 0 < d n;
  interval_ladder_decreases : forall n, d n.+1 < d n;
  interval_ladder_gap : forall n, d n - d n.+1 < e;
  interval_ladder_small : forall r, 0 < r -> exists n, d n < r
}.

(** Source for [interval_ladder_antitone]: supporting nesting
    of the interval endpoints in Federer 2.2.9, p. 65;
    derived from the abstract ladder's successive strict inequalities. *)
Lemma interval_ladder_antitone (R : realType) (h e : R) (d : nat -> R)
    (hd : is_small_interval_ladder h e d) i j :
  (i <= j)%N -> d j <= d i.
Proof.
move=> hij; elim: j hij=> [|j IH] hij.
- have -> : i = 0%N by apply/eqP; rewrite -leqn0.
  exact: lexx.
- case: (eqVneq i j.+1)=> [->|hne]; first exact: lexx.
  apply: le_trans (ltW (interval_ladder_decreases hd j)) _.
  apply: IH; by move: hij; rewrite leq_eqVlt (negbTE hne) /= ltnS.
Qed.

(** Source for [interval_ladder_crossing]: supporting cover
    argument for Federer 2.2.9, p. 65: every positive number
    below the half-length lies between two consecutive ladder
    points. The upper endpoint is included, so only the countable
    set of endpoints can be lost by using open intervals. *)
Lemma interval_ladder_crossing (R : realType) (h e : R) (d : nat -> R)
    (hd : is_small_interval_ladder h e d) r :
  0 < r -> r < h -> exists n, d n.+1 < r /\ r <= d n.
Proof.
move=> hr hrh; have [N hN] := interval_ladder_small hd hr.
have hex : exists n, d n < r by exists N.
have [k hk hmin] := ex_minnP hex.
case: k hk hmin=> [|k] hk hmin.
- by move: hk; rewrite (interval_ladder_start hd) ltNge (ltW hrh).
- exists k; split=> //; rewrite leNgt; apply/negP=> hkr.
  have := hmin k hkr; by rewrite leqNgt ltnSn.
Qed.
