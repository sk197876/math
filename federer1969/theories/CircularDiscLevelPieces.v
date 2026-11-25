(** Federer (1969), 3.3.19, pp. 302–304:
    the actual original limiting set is partitioned by its
    original level pieces. Prove uniqueness, exact disjointness
    and the small-diameter estimates used below. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscTreeTopology CircularDiscTreeSeparation CircularDiscLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pieces.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_level_point_unique]: every
    point of an original level union belongs to exactly
    one original closed disc, supporting the partitions
    and the original eta_n in 3.3.19, pp. 304–305. *)
Lemma circular_disc_level_point_unique j (x z w:E):
  z \in H j ->w \in H j ->
  metric_closed_ball z (rho j) x ->metric_closed_ball w (rho j) x ->z=w.
Proof.
move=>hz hw hx hy;case:(eqVneq z w)=>[h|hne];first exact h.
have hGap:=@circular_disc_tree_separation R H hH j z w hz hw hne x x hx hy.
rewrite mdistxx in hGap.
have hFalse:=lt_trans (@factorial_disc_radius_positive R N rho hs j) hGap.
by rewrite ltxx in hFalse.
Qed.

(** Source for [circular_disc_level_disjoint]: distinct
    original closed level discs are disjoint, as used
    in the finite psi_n sum in 3.3.19, p. 304. *)
Lemma circular_disc_level_disjoint j (z w:E):
  z \in H j ->w \in H j ->z!=w ->
  metric_closed_ball z (rho j) `&` metric_closed_ball w (rho j) = set0.
Proof.
move=>hz hw hZW;apply/seteqP;split=>[x [hx hy]|x []].
have hEqual:=@circular_disc_level_point_unique j x z w hz hw hx hy.
by move:hZW;rewrite hEqual eqxx.
Qed.

(** Source for [circular_disc_within_ball_distance]: the
    actual closed level disc has point-pair distances at
    most twice its original radius, supporting the small
    cover and relative-basis arguments of 3.3.19,
    pp. 303–304. *)
Lemma circular_disc_within_ball_distance j (z x y:E):
  metric_closed_ball z (rho j) x ->metric_closed_ball z (rho j) y ->
  mdist x y<=2* rho j.
Proof.
move=>hx hy;have hh:=metric_triangle x z y.
have hx':mdist x z<=rho j by rewrite metric_sym;exact hx.
change (is_true (mdist z y<=rho j)) in hy;lra.
Qed.
End Pieces.
