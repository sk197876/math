(** Federer (1969), 3.3.19, p. 303: the
    actual radial retraction has optimal Lipschitz constant one. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  CircularUnitVectors RadialBallRetractionUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_radial_retraction_optimal]: the
    exact printed Lip(f)=1 in 3.3.19, p. 303.
    Two distinct original fixed points give minimality;
    nonexpansion follows from the independent retraction laws.
    The positive-radius condition is satisfied by every
    actual original retraction ball. *)
Theorem planar_radial_retraction_optimal (R:realType)
    (z:inner_metric_space (@euclidean_inner_productP R 2)) (r:R) P:
  0<r ->@is_radial_ball_retraction R (R_n R 2) (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2) z r P ->
  is_least_metric_lipschitz_constant setT P 1.
Proof.
move=>hr hP;constructor;first exact:radial_ball_retraction_nonexpanding hP.
move=>M [_ hM].
pose u:=@circular_unit_vector R 0.
have hDistance:mdist (z+r*:u) z=r.
  by rewrite inner_metric_distanceE addrAC subrr add0r inner_normZ circular_unit_vector_norm
    mulr1 (ger0_norm (ltW hr)).
have hZ:metric_closed_ball z r z.
  change (is_true (mdist z z<=r));rewrite mdistxx;exact:ltW hr.
have hU:metric_closed_ball z r (z+r*:u).
  change (is_true (mdist z (z+r*:u)<=r));by rewrite metric_sym hDistance.
have h:=hM (z+r*:u) z Logic.I Logic.I.
rewrite (radial_ball_retraction_fixed hP hU) (radial_ball_retraction_fixed hP hZ) hDistance in h.
by move:h;rewrite -{1}(mul1r r) ler_pM2r.
Qed.
