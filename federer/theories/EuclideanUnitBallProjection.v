(** Federer (1969), 3.2.35, pp. 271--272:
    the actual projected unit balls and their
    boundary normalization in Steiner's constants. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerConvex EuclideanNormSetDistance EuclideanDistanceTubeBoundary EuclideanDistanceTubeConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionImageLifting MetricClosedBalls
  CoveringFamilyUP CoveringFamilyLaws MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_unit_ball_projection]: actual
    orthogonal projections send the open unit
    ball onto the open target unit ball,
    supporting the coefficient normalization of
    Federer 3.2.35, p. 272. Contraction
    proves inclusion, and exact-distance lifting
    at zero proves the reverse. *)
Lemma euclidean_unit_ball_projection (R:realType) n m
    (p:orthogonal_projection_metric_space R n m):
  euclidean_projection_linear p @` [set x|inner_norm (@euclidean_inner_productP R n) x<1]=
    [set y|inner_norm (@euclidean_inner_productP R m) y<1].
Proof.
apply/seteqP; split=>y.
- move=>[x hx <-].
  have hBound:=euclidean_projection_nonexpanding p x 0.
  rewrite linear0 !inner_metric_distanceE !subr0 in hBound.
  exact:le_lt_trans hBound hx.
- move=>hy.
  have [x [hImage hDistance]]:=@orthogonal_projection_exact_distance_lift R n m p 0 y.
  exists x=>//.
  rewrite linear0 !inner_metric_distanceE !sub0r !inner_normN in hDistance.
  change (is_true (inner_norm (@euclidean_inner_productP R n) x<1)).
  by rewrite hDistance.
Qed.

(** Source for [euclidean_unit_ball_boundary]: the
    whole boundary of the open unit ball
    is its unit sphere, supporting Cauchy
    normalization in Federer 3.2.35, pp. 271--272.
    The proved exact distance-level boundary theorem
    applies to the actual singleton-centre distance. *)
Lemma euclidean_unit_ball_boundary (R:realType) n:
  let B:set (inner_metric_space (@euclidean_inner_productP R n)):=
    [set x|inner_norm (@euclidean_inner_productP R n) x<1] in
  closure B `\` interior B=[set x|inner_norm (@euclidean_inner_productP R n) x= 1].
Proof.
move=>B; exact:(@euclidean_distance_tube_boundary R n [set 0]
  (inner_norm (@euclidean_inner_productP R n)) 1 (ex_intro _ 0 erefl)
  (@euclidean_norm_set_distance R n) ltr01).
Qed.

(** Source for [euclidean_unit_ball_convex_bounded]:
    the original body hypotheses for the unit
    ball used to normalize Steiner coefficients,
    Federer 3.2.35, pp. 271--272. Actual
    norm zero, metric ball topology, tube
    convexity and a finite closed-ball bound
    discharge all hypotheses, including dimension zero. *)
Lemma euclidean_unit_ball_convex_bounded (R:realType) n:
  let B:set (inner_metric_space (@euclidean_inner_productP R n)):=
    [set x|inner_norm (@euclidean_inner_productP R n) x<1] in
  B!=set0 /\open B /\is_inner_convex B /\metric_set_bounded B.
Proof.
move=>B.
have hBall:B=[set x:inner_metric_space (@euclidean_inner_productP R n)|mdist (0:inner_metric_space (@euclidean_inner_productP R n)) x<1].
  apply/seteqP; split=>x; by rewrite /= inner_metric_distanceE sub0r inner_normN.
split; first by exists 0; change (is_true (inner_norm (@euclidean_inner_productP R n) 0<1)); rewrite inner_norm0.
split; first by rewrite hBall; exact:metric_open_ball_open.
split.
- apply:(@euclidean_distance_tube_convex R n [set 0]
    (inner_norm (@euclidean_inner_productP R n)) 1 (euclidean_norm_set_distance R n)).
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scaler0.
- apply:(@metric_bounded_subset R _ B (metric_closed_ball (0:inner_metric_space (@euclidean_inner_productP R n)) 1)); last exact:covering_closed_ball_bounded ler01.
  move=>x hx; change (is_true (mdist (0:inner_metric_space (@euclidean_inner_productP R n)) x<=1)); rewrite inner_metric_distanceE sub0r inner_normN.
  exact:ltW hx.
Qed.
