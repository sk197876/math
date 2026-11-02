(** The radius cap implicit in the use of 2.8.15 in Federer (1969), 2.8.18,
    p. 152. A family of all positive-radius balls need not have bounded
    radii, so restrict it before applying Federer's original small-family
    formulation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls CenteredBallCoverUP CenteredBallFineness
  DirectionalLimitationUP SmallRadiusNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [capped_closed_ball_family]: the small-ball
    family required for the application of 2.8.15 in
    Federer 2.8.18, p. 152. Membership retains F and
    a positive radius representation strictly below mu. *)
Definition capped_closed_ball_family (R : realType) (X : metricType R)
    (F : set (set X)) (mu : R) :=
  [set S | F S /\ exists x r, 0 < r < mu /\ S = metric_closed_ball x r].

(** Source for [capped_closed_balls_small_family]: supporting
    small-family clause for the use of 2.8.15 in Federer
    2.8.18, p. 152. The bound is on a representation,
    without asserting uniqueness of the center or radius. *)
Lemma capped_closed_balls_small_family (R : realType) (X : metricType R)
    (F : set (set X)) (mu : R) :
  is_small_closed_ball_family mu (capped_closed_ball_family F mu).
Proof. by move=> S [_ h]. Qed.

(** Source for [capped_closed_balls_remain_fine]: supporting
    radius-infimum clause for the use of 2.8.15 in Federer
    2.8.18, p. 152. Choose a centered radius below
    min(epsilon,mu), preserving arbitrary radius fineness. *)
Lemma capped_closed_balls_remain_fine (R : realType) (X : metricType R)
    (F : set (set X)) (A : set X) (mu : R) :
  0 < mu -> has_arbitrarily_small_centered_balls F A ->
  has_arbitrarily_small_centered_balls (capped_closed_ball_family F mu) A.
Proof.
move=> hm hf x hx e he.
have hmin : 0 < Num.min e mu by rewrite lt_min he hm.
have [r [/andP [hr hrmin] hF]] := hf x hx _ hmin.
have hme : Num.min e mu <= e by rewrite ge_min lexx.
have hre : r < e := lt_le_trans hrmin hme.
have hmm : Num.min e mu <= mu by rewrite ge_min lexx orbT.
have hrm : r < mu := lt_le_trans hrmin hmm.
exists r; split; first by rewrite hr hre.
split=> //; exists x,r; split=> //; by rewrite hr hrm.
Qed.

(** Source for [positive_directional_radius_cap]: the choice
    of 0<mu<xi/2 needed to apply 2.8.15 in Federer
    2.8.18, p. 152. Xi may be infinity; no finite
    upper bound on the directional radius is introduced. *)
Lemma positive_directional_radius_cap (R : realType) (xi : \bar R) :
  (0 < xi)%E -> exists mu : R, 0 < mu /\ (mu%:E < (1/2 : R)%:E * xi)%E.
Proof.
move=> hx; case: xi hx=> [q| |] hx; last by [].
- have hq : (0 < q)%R by move: hx; rewrite lte_fin.
  exists (q/4); split; first by rewrite divr_gt0 // ltr0n.
  rewrite extended_half_radius_boundE lte_fin -mulrDl ltr_pdivrMr ?ltr0n //.
  by rewrite -mulr2n -(mulr_natr q 2) ltr_pM2l // ltr_nat.
- exists 1; split; first exact: ltr01.
  rewrite extended_half_radius_boundE; exact: ltry.
Qed.
