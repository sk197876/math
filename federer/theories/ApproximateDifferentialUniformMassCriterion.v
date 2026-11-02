(** Federer (1969), 3.1.4, p. 216: the estimates with
    errors K/j and exceptional mass at most C r^m/j imply approximate
    differentiability. K=2m and C=m 2^(m+1) give the printed constants. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNorm RealNormUP EuclideanLebesgueDimensions EuclideanBallVolume
  EuclideanClosedBallVolume EuclideanNoncenteredVitali MetricClosedBalls
  MeasureUP MeasureBasic CenteredZeroDensityCriterion ExtendedRealReciprocalBounds
  ApproximateDifferentialUP ApproximateDifferentialIncrementCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_uniform_mass_criterion]:
    the last two displays and concluding inference in Federer 3.1.4,
    p. 216. Both the remainder tolerance and relative exceptional
    mass tend to zero; no differentiability premise is introduced. *)
Theorem approximate_differential_uniform_mass_criterion (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (f : R_n R n.+1 -> Y) (a : R_n R n.+1) (L : Hom (R_n R n.+1) Y)
    (K C : R) :
  0<=K -> 0<=C ->
  (forall j : nat, exists d : R, 0<d /\ forall r : R, 0<r -> r<d ->
    (euclidean_lebesgue_measure n.+1
      ([set h | (K*(j.+1%:R)^-1)*inner_norm (@euclidean_inner_productP R n.+1) h <
        NY (f (a+h)-f a-L h)]%R `&` metric_closed_ball
          (0%R : inner_metric_space (@euclidean_inner_productP R n.+1)) r)
      <= (C*(j.+1%:R)^-1*r^+n.+1)%R%:E)%E) ->
  has_approximate_differential NY setT f a L.
Proof.
move=> hK hC hs; apply: (approximate_differential_increment_density_criterion hNY)=> e he.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose NX := inner_norm (@euclidean_inner_productP R n.+1).
pose vol := euclidean_unit_ball_volume R n.+1.
have hv : 0<vol := (euclidean_unit_ball_volumeE R n.+1).2.
apply: (@centered_small_mass_zero_density R [the metricType R of X]
  (@euclidean_lebesgue_measure R n.+1) _ 0 (euclidean_lebesgue_is_measure R n.+1)).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- move=> c hc.
  have hk1 : 0<K+1 by rewrite ltr_wpDl.
  have hc1 : 0<C+1 by rewrite ltr_wpDl.
  have hcut : 0<Num.min (e/(K+1)) (c*vol/(C+1)).
    by rewrite lt_min !divr_gt0 ?mulr_gt0.
  have [j hj] := positive_reciprocal_nat_small hcut.
  have hjp : 0<(j.+1%:R : R)^-1 by rewrite invr_gt0 ltr0n.
  have [hje hjc] : (j.+1%:R)^-1<e/(K+1) /\ (j.+1%:R)^-1<c*vol/(C+1).
    by move: hj; rewrite lt_min=> /andP.
  have hje' : K*(j.+1%:R)^-1<e.
    apply: le_lt_trans (_ : K*(j.+1%:R)^-1<=(K+1)*(j.+1%:R)^-1) _.
    + rewrite mulrDl mul1r lerDl; exact: ltW hjp.
    + by move: hje; rewrite ltr_pdivlMr // mulrC.
  have hjc' : C*(j.+1%:R)^-1<c*vol.
    apply: le_lt_trans (_ : C*(j.+1%:R)^-1<=(C+1)*(j.+1%:R)^-1) _.
    + rewrite mulrDl mul1r lerDl; exact: ltW hjp.
    + by move: hjc; rewrite ltr_pdivlMr // mulrC.
  have [d [hd hmass]] := hs j.
  exists d; split=> // r hr hrd.
  have hsub : [set h : X | e*NX h<NY (f (a+h)-f a-L h)]%R `&` metric_closed_ball (0 : X) r `<=`
      [set h : X | (K*(j.+1%:R)^-1)*NX h<NY (f (a+h)-f a-L h)]%R `&` metric_closed_ball (0 : X) r.
    move=> h [hh hb]; split=> //.
    apply: le_lt_trans _ hh; apply: ler_wpM2r.
    - exact: inner_norm_nonnegative.
    - exact: ltW hje'.
  apply: le_lt_trans (le_trans (measure_mono (euclidean_lebesgue_is_measure R n.+1) hsub)
    (hmass r hr hrd)) _.
  rewrite (euclidean_closed_ball_normalized_volume (0 : X) (ltW hr)) -EFinM lte_fin mulrA.
  by rewrite ltr_pM2r ?exprn_gt0.
Qed.
