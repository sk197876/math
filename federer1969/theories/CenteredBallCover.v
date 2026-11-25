(** Federer (1969), Theorem 2.8.14, p. 150: choose tau as in 2.8.11, select
    controlled parameters with 2.8.13, and decompose the associated balls by
    2.8.12. All selected witnesses are used through their abstract laws. we
    retain the book's strict bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls ControlledBallParameters DirectionalLimitationUP
  DirectionalCoverCardinality RadiusCoverSelectionUP ControlledCenterSelectionUP
  ControlledCenterSelection BallFamilyDecompositionUP ControlledBallDecomposition
  CenteredBallCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [small_centered_balls_finite_disjoint_cover]: the
    proof of Federer 2.8.14, p. 150, uses only the existence
    of an eligible small ball at each target center. This
    supporting strengthening allows other sets in F, since they
    do not enter the selected parameter family. The book theorem
    with F a family of small closed balls is stated below. *)
Theorem small_centered_balls_finite_disjoint_cover (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta mu : R) (zeta : nat) (F : set (set X)) :
  is_directionally_limited_at A xi eta zeta -> (0 < mu)%R ->
  (mu%:E < (1/2 : R)%:E * xi)%E -> has_small_centered_balls mu F A ->
  exists G : 'I_(2*zeta+1) -> set (set X), is_finite_disjoint_ball_cover F A G.
Proof.
move=> hlim hm hsmall hcent.
have [tau hfactor] := directional_cover_factor_exists (directional_separation_range hlim).
have ht : 1 < tau := hfactor.1.
pose P : set (X*R) := [set p | A p.1 /\ 0 < p.2 < mu /\ F (parameter_closed_ball p)].
have hP : is_bounded_positive_radius_family mu P by move=> p hp; exact: hp.2.1.
have [Q hs] := @federer_2_8_13 R X tau mu P ht hm hP.
have hQctrl := controlled_center_selection_controlled hs.
have hQP : Q `<=` P := controlled_center_selection_members hs.
have hQA q : Q q -> A q.1 by move=> hq; exact: (hQP q hq).1.
have hQbound : is_bounded_positive_radius_family mu Q by move=> q hq; exact: (hQP q hq).2.1.
have [G hG] := @federer_2_8_12 R X A xi eta tau mu zeta Q
  hlim hfactor hm hQctrl hQA hQbound hsmall.
exists G; constructor.
- move=> i B hB.
  have [q hq <-] := @ball_decomposition_members X (associated_closed_ball_family Q)
    (2*zeta+1)%N G hG i B hB.
  exact: (hQP q hq).2.2.
- exact: ball_decomposition_disjoint hG.
- move=> a ha.
  have [r [hr hF]] := hcent a ha.
  have hp : P (a,r) by split=> //; split.
  have [q [hq hcov]] := @controlled_center_selection_covers R X tau P Q hs (a,r) hp.
  have hball : associated_closed_ball_family Q (parameter_closed_ball q) by exists q.
  rewrite (ball_decomposition_covers hG) in hball.
  have [i hi hgi] := hball; exists i=> //.
  by exists (parameter_closed_ball q).
Qed.

(** Source for [federer_2_8_14]: the complete covering theorem
    of Federer 2.8.14, p. 150. F is a family of small
    positive-radius closed balls and each target point has such
    a ball centered at it. With directional limitation and
    0<mu<xi/2, A is covered by 2 zeta+1 disjointed subfamilies
    of F. Neither countability nor any measure is assumed. *)
Theorem federer_2_8_14 (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta mu : R) (zeta : nat) (F : set (set X)) :
  is_directionally_limited_at A xi eta zeta -> (0 < mu)%R ->
  (mu%:E < (1/2 : R)%:E * xi)%E -> is_small_closed_ball_family mu F ->
  has_small_centered_balls mu F A ->
  exists G : 'I_(2*zeta+1) -> set (set X), is_finite_disjoint_ball_cover F A G.
Proof.
move=> hlim hm hsmall _ hcent.
exact: small_centered_balls_finite_disjoint_cover hlim hm hsmall hcent.
Qed.
