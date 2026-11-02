(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra lra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter CoveringFamilyUP MetricClosedBalls
  CoveringFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [metric_bounded_distance_bound]: metric background
    for bounded supports in Federer 2.9.10, p. 157. A bounded
    set has a finite distance bound from any fixed base point,
    including the empty set. This supports closure of the printed
    lattice, not an additional separately stated book theorem. *)
Lemma metric_bounded_distance_bound (R : realType) (X : metricType R) (A : set X) (a : X) :
  metric_set_bounded A -> exists r : R, (0<=r)%R /\ forall x, A x -> (mdist a x<=r)%R.
Proof.
move=> hA; case: (pselect (A !=set0))=> [[b hb]|hzero].
- have hd0 := metric_diameter_nonnegative (extended_metric_diameter_specification A).
  have hfin : extended_metric_diameter A \is a fin_num by rewrite (ge0_fin_numE hd0).
  pose d := fine (extended_metric_diameter A).
  have he : extended_metric_diameter A=d%:E by rewrite /d fineK.
  have hd : (0<=d)%R by move: hd0; rewrite he lee_fin.
  exists (mdist a b+d)%R; split; first exact: addr_ge0 (mdist_ge0 _ _) hd.
  move=> x hx; apply: le_trans (metric_triangle a b x) _.
  apply: lerD (lexx _) _.
  have h := metric_diameter_upper (extended_metric_diameter_specification A) hb hx.
  by move: h; rewrite he lee_fin.
- exists 0%R; split; first exact: lexx.
  by move=> x hx; exfalso; apply: hzero; exists x.
Qed.

(** Source for [metric_bounded_union]: metric background for
    addition, minimum and subtraction in the bounded-support
    lattice of Federer 2.9.10, p. 157. The union of two bounded
    sets is bounded, without any properness or dimension assumption. *)
Lemma metric_bounded_union (R : realType) (X : metricType R) (A B : set X) :
  metric_set_bounded A -> metric_set_bounded B -> metric_set_bounded (A `|` B).
Proof.
move=> hA hB; case: (pselect (A !=set0))=> [[a ha]|hzero].
- have [r [hr hAr]] := metric_bounded_distance_bound a hA.
  have [s [hs hBs]] := metric_bounded_distance_bound a hB.
  have ht : (0<r+s+1)%R by lra.
  have hsub : A `|` B `<=` metric_closed_ball a (r+s+1)%R.
    move=> x [hx|hx].
    + apply: le_trans (hAr x hx) _; lra.
    + apply: le_trans (hBs x hx) _; lra.
  exact: le_lt_trans (@extended_metric_diameter_mono R X (A `|` B) (metric_closed_ball a (r+s+1)%R) hsub)
    (@covering_closed_ball_bounded R X a (r+s+1)%R (ltW ht)).
- have he : A=set0.
    apply/seteqP; split=> x; [move=> hx; exfalso; apply: hzero; by exists x|by move=> []].
  by rewrite he set0U.
Qed.
