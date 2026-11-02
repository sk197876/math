(** Federer (1969), 2.10.39, printed p. 199: sum the m-th diameter costs of
    the finitely many balls covering a subdivided box. This supporting
    cutoff estimate applies to every metric space and allows radius zero
    through an arbitrarily small positive enlargement inside a strict cutoff
    margin. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import MetricClosedBalls HausdorffMeasureUP HausdorffDiameterCost
  EuclideanBallVolume MetricScaleEnvelopeUP MetricScaleCutoffCost
  SphericalScaleBallBound FiniteCoverMeasureBounds MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_cutoff_finite_equal_ball_cover]: supporting
    finite sum of ball costs in 2.10.39, p. 199.
    The conclusion bounds the actual size-d approximation,
    not the final spherical measure of a fixed box.
    No measurability hypothesis is imposed on the target. *)
Theorem spherical_cutoff_finite_equal_ball_cover (R : realType) (X : metricType R)
    (I : finType) m (centre : I -> X) (r d : R)
    (nu : set X -> \bar R) (A : set X) :
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) d%:E nu ->
  0<=r -> r+r<d -> A `<=` \bigcup_i metric_closed_ball (centre i) r ->
  (nu A<=(#|I|%:R*(euclidean_unit_ball_volume R m*r^+m))%:E)%E.
Proof.
move=> hn hr hd hcover.
have hm : is_measure nu := metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative m (val j)).
have hh := @measure_finite_indexed_cover R X I nu hm A
  (fun i=>metric_closed_ball (centre i) r) hcover.
have he : (\sum_(i : I) (euclidean_unit_ball_volume R m*r^+m)%:E)%E=
    (#|I|%:R*(euclidean_unit_ball_volume R m*r^+m))%:E.
  rewrite sumEFin sumr_const cardT; congr (_%:E); symmetry; exact: mulr_natl.
rewrite -he; apply: le_trans hh _; apply: lee_sum=> i _.
exact: spherical_scale_closed_ball_bound hn hr hd.
Qed.
