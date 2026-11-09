(** Federer (1969), 3.3.4, p. 291: the
    almost-everywhere density-one conclusion of
    3.2.19 becomes an every-point assertion by
    transitive isometric invariance and positive
    total reference mass. Prove that implication;
    do not strengthen the premise of 3.2.19. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import MeasureAlmostUP MetricDensities MetricClosedBalls PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_measure_almost_truth_point]:
    the existence of an actual density-one point
    used in Federer 3.3.4, p. 291: a
    conull truth set in a positive-mass space
    is nonempty. No global point is selected. *)
Lemma positive_measure_almost_truth_point (R:realType) (X:choiceType)
    (mu:set X->\bar R) (P:set X):
  0<mu setT ->measure_almost_everywhere mu P ->exists x,P x.
Proof.
move=>hPositive hAlmost; apply:contrapT=>hNone.
have he:~` P=setT.
  apply/seteqP; split=>x; first by [].
  move=>_ hx; apply:hNone; by exists x.
rewrite /measure_almost_everywhere he in hAlmost.
by move:hPositive; rewrite hAlmost ltxx.
Qed.

(** Source for [metric_density_center_independent]:
    centre-independent actual reference ball masses
    give the same common density graph at
    every point, supporting Federer 3.3.4,
    p. 291. Both one-sided limits remain literal. *)
Lemma metric_density_center_independent (R:realType) (X:metricType R)
    (mu:set X->\bar R) m (x y:X) (c: \bar R):
  (forall r:R,mu (metric_closed_ball x r)=mu (metric_closed_ball y r)) ->
  partial_function_graph (metric_density m mu) x c <->
    partial_function_graph (metric_density m mu) y c.
Proof.
move=>hBalls.
have hF:metric_ball_density m mu x=metric_ball_density m mu y.
  apply:funext=>r; by rewrite /metric_ball_density hBalls.
rewrite !metric_density_graph /upper_metric_density /lower_metric_density hF.
reflexivity.
Qed.

(** Source for [homogeneous_metric_density_from_almost]:
    the every-point density assertion of Federer
    3.3.4, p. 291, follows from the actual
    almost-everywhere conclusion and centre-independent
    ball masses. Neither every-point density nor
    a selected point is a premise. *)
Theorem homogeneous_metric_density_from_almost (R:realType) (X:metricType R)
    (mu:set X->\bar R) m (c: \bar R):
  0<mu setT ->
  (forall x y r,mu (metric_closed_ball x r)=mu (metric_closed_ball y r)) ->
  measure_almost_everywhere mu [set x|partial_function_graph (metric_density m mu) x c] ->
  forall x,partial_function_graph (metric_density m mu) x c.
Proof.
move=>hPositive hBalls hAlmost x.
have [y hy]:=positive_measure_almost_truth_point hPositive hAlmost.
exact:(@metric_density_center_independent R X mu m y x c (hBalls y x)).1 hy.
Qed.
