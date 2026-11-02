(** Federer (1969), 2.2.9, p. 65: disjoint nonempty open children whose
    closures remain in an open parent. This supporting binary split can be
    iterated on one remainder to obtain countably many disjoint children. It
    uses no separability assumption. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls NoIsolatedPoints MetricOpenShrinking.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonisolated_open_binary_split]: supporting construction for
    Federer 2.2.9, p. 65: every nonempty open parent contains two nonempty
    open sets with disjoint closures and arbitrarily small diameters. *)
Lemma nonisolated_open_binary_split (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (U : set T) e :
  open U -> U !=set0 -> 0 < e -> exists A B : set T,
    open A /\ open B /\ A !=set0 /\ B !=set0 /\
    closure A `<=` U /\ closure B `<=` U /\
    closure A `&` closure B = set0 /\
    (forall x y, closure A x -> closure A y -> mdist x y < e) /\
    (forall x y, closure B x -> closure B y -> mdist x y < e).
Proof.
move=> ho [a ha] he.
have [r [hr hball]] := metric_open_contains_closed_ball ho ha.
have [b [hab hbr]] := nonisolated_metric_point_near hT a hr.
have hb : U b := hball b (ltW hbr).
pose d := Order.min e (mdist a b / 2).
have hd : 0 < d by rewrite /d lt_min he divr_gt0 ?hab ?ltr0n.
have hde : d <= e by rewrite /d ge_min lexx.
have hdb : d <= mdist a b / 2 by rewrite /d ge_min lexx orbT.
have [A [hAo [hAa [hAU hAd]]]] := metric_small_open_with_closed_parent ho ha hd.
have [B [hBo [hBb [hBU hBd]]]] := metric_small_open_with_closed_parent ho hb hd.
exists A, B; split=> //; split=> //; split; first by exists a.
split; first by exists b.
split=> //; split=> //; split.
- apply/seteqP; split; last by move=> x [].
  move=> x [hxA hxB].
  have hax := hAd a x (subset_closure hAa) hxA.
  have hxb := hBd x b hxB (subset_closure hBb).
  have hsum := ltrD hax hxb.
  have htwo : d+d <= mdist a b.
    have hh := lerD hdb hdb; by rewrite -splitr in hh.
  have hh := le_lt_trans (metric_triangle a x b) (lt_le_trans hsum htwo).
  by move: hh; rewrite ltxx.
- split.
  + move=> x y hx hy; exact: lt_le_trans (hAd x y hx hy) hde.
  + move=> x y hx hy; exact: lt_le_trans (hBd x y hx hy) hde.
Qed.
