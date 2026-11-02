(** Federer (1969), 2.10.40, printed p. 200: every positive unit-direction
    perturbation of the unique minimum centre violates one prescribed ball.
    The violating pair has arbitrarily small slack and directional
    coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  WeightedBallMinimumUP WeightedBallMinimumUniqueness WeightedBallContactProfiles
  InnerUnitPerturbationSquare UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_minimum_perturbation_violates]: direct
    epsilon u not in Y_c step in 2.10.40,
    p. 200, before the choice of a violating
    pair. Uniqueness is proved from the minimum laws;
    it is not an interface assumption. *)
Lemma weighted_ball_minimum_perturbation_violates (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n)
    (u : inner_metric_space (@euclidean_inner_productP R n)) (e : R) :
  compact P -> P !=set0 -> positive_ball_parameter_family P -> is_weighted_ball_minimum P D ->
  euclidean_inner_product u u= 1 -> 0<e -> exists p, P p /\
    p.2*weighted_minimum_scale D<inner_norm (@euclidean_inner_productP R n)
      (weighted_minimum_centre D+e*:u-p.1).
Proof.
move=> hP hne hpos hD hu he.
pose b := weighted_minimum_centre D.
pose c := weighted_minimum_scale D.
have hunit : inner_norm (@euclidean_inner_productP R n) u= 1 := unit_normal_norm _ hu.
have hu0 : u!=0.
  by rewrite -(@inner_norm_gt0 R _ _ (@euclidean_inner_productP R n) u) hunit ltr01.
have hshift : e*:u!=0 by rewrite scaler_eq0 (gt_eqF he) (negbTE hu0).
have hmove : b+e*:u!=b.
  apply/eqP=> hh.
  have hv := congr1 (fun z=>z-b) hh.
  rewrite addrAC subrr add0r in hv.
  by move: hshift; rewrite hv eqxx.
have hnot : ~ weighted_ball_centres P c (b+e*:u).
  move=> hfeasible.
  have hh := @weighted_ball_minimum_centres_unique R n P D hP hne hpos hD
    (b+e*:u) b hfeasible (weighted_minimum_feasible_law hD).
  by move: hmove; rewrite hh eqxx.
apply: contrapT=> hnone; apply: hnot=> p hp.
rewrite leNgt; apply/negP=> hbad.
apply: hnone; by exists p.
Qed.

(** Source for [weighted_ball_perturbation_profile_bounds]: direct
    small-slack and halfspace estimates for the violating
    pair in 2.10.40, p. 200. The triangle
    inequality gives slack less than epsilon; the
    squared unit-shift identity gives u dot (a-b)<epsilon/2. *)
Lemma weighted_ball_perturbation_profile_bounds (R : realType) n P
    (b u : inner_metric_space (@euclidean_inner_productP R n)) (c e : R) p :
  positive_ball_parameter_family P -> weighted_ball_centres P c b -> 0<=c ->
  euclidean_inner_product u u= 1 -> 0<e -> P p ->
  p.2*c<inner_norm (@euclidean_inner_productP R n) (b+e*:u-p.1) ->
  weighted_ball_slack b c p<e /\ weighted_ball_direction u b p<e/2.
Proof.
move=> hP hb hc hu he hp hbad.
pose N := inner_norm (@euclidean_inner_productP R n).
have hunit : inner_norm (@euclidean_inner_productP R n) u= 1 := unit_normal_norm _ hu.
have hre : 0<=p.2*c := mulr_ge0 (ltW (hP p hp)) hc.
have htri := @inner_norm_triangle R _ _ (@euclidean_inner_productP R n) (b-p.1) (e*:u).
rewrite inner_normZ hunit mulr1 (ger0_norm (ltW he)) in htri.
have heq : (b-p.1)+e*:u=b+e*:u-p.1 by rewrite addrAC.
rewrite heq in htri.
split.
- have hh := lt_le_trans hbad htri.
  rewrite /weighted_ball_slack ltrBlDr addrC; exact hh.
- have hleft : N (b-p.1)^+2<=(p.2*c)^+2.
    by rewrite (ler_sqr (inner_norm_nonnegative _ _) hre); exact: hb p hp.
  have hright : (p.2*c)^+2<N (b+e*:u-p.1)^+2.
    by rewrite (ltr_sqr hre (inner_norm_nonnegative _ _)).
  have hquad := @inner_unit_perturbation_square R _ _ (@euclidean_inner_productP R n) u b p.1 e hu.
  change (N (b+e*:u-p.1)^+2=e^+2+N (b-p.1)^+2-2*e*euclidean_inner_product u (p.1-b)) in hquad.
  rewrite /weighted_ball_direction; nra.
Qed.
