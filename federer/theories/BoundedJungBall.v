(** Federer (1969), 2.10.41, printed p. 200: pass from a bounded source to
    its compact closure, apply the compact contact-point proof, then return
    the enclosing ball and its uniqueness to the source. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  MetricDiameterUP MetricDiameter MetricDiameterClosure EuclideanBoundedClosure
  EuclideanMinimumBallUP EuclideanMinimumBallLaws MinimumBallClosure CompactJungBall JungConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_jung_minimum_ball]: direct
    full closure reduction for 2.10.41, p. 200.
    Any finite nonnegative real upper bound for the
    source diameter is allowed, including zero; no
    compactness, closedness or measurability premise is
    added to the original source. The minimum laws
    have a unique centre and radius. *)
Theorem bounded_jung_minimum_ball (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (d : R) :
  S !=set0 -> 0<=d -> (extended_metric_diameter S<=d%:E)%E ->
  exists b r, is_minimum_enclosing_ball S b r /\ r+r<=@jung_factor R n*d /\
    forall z t, is_minimum_enclosing_ball S z t -> z=b /\ t=r.
Proof.
move=> hne hd hdiam.
pose C := closure S.
have hC : compact C := @euclidean_bounded_set_closure_compact R n S d hne hdiam.
have hCne : C !=set0.
  have [a ha] := hne; exists a; exact: subset_closure ha.
have hCd : (extended_metric_diameter C<=d%:E)%E by rewrite /C extended_metric_diameter_closure.
have hpair a a' : C a -> C a' -> inner_norm (@euclidean_inner_productP R n) (a-a')<=d.
  move=> ha ha'.
  have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification C) ha ha') hCd.
  by move: hh; rewrite lee_fin inner_metric_distanceE.
have [b [r [hmin hbound]]] := @compact_jung_minimum_ball R n C d hC hCne hd hpair.
exists b,r; split; first exact: minimum_ball_source_laws hmin.
split=> // z t hzt.
exact (@minimum_enclosing_ball_unique R n C z t b r hC hCne
  (minimum_ball_closure_laws hzt) hmin).
Qed.
