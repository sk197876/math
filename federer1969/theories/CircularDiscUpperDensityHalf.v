(** Federer (1969), 3.3.19, p. 306: complete
    the final actual upper one-density value one half
    for the original Hausdorff restriction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscLateBallMass CircularDiscUpperDensityLower HausdorffMeasure MeasureUP MeasureBasic MeasureRestriction
  MetricDensities EuclideanBallVolume PositiveRadiusLimitBounds ExtendedScaledErrorBound
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_upper_density_at_most_half]:
    the upper bound in the final assertion of
    3.3.19, p. 306. Uniform actual late-ball masses,
    the actual denominator 2t and all positive-radius
    order limits prove it at EVERY original a in A.
    No density conclusion or sampled-radius bound is
    supplied as a premise. *)
Theorem circular_disc_upper_density_at_most_half (a:E):A a ->
  (upper_metric_density 1 (measure_restrict mu A) a<=((1:R)/2)%:E)%E.
Proof.
move=>ha.
apply:(@extended_upper_bound_from_scaled_errors R _ (1/2) 1 ler01)=>e he.
rewrite !mul1r.
have hTwice:0<2* e by lra.
have [delta [hDelta hMass]]:= @circular_disc_uniform_late_ball_mass R H hH A hA (2* e) hTwice.
rewrite /upper_metric_density.
apply:(@positive_radius_upper_eventual_bound R (metric_ball_density 1 (measure_restrict mu A) a) _ delta hDelta)=>t /andP[ht htSmall].
have hBound:= hMass a t ha ht htSmall.
have hDen:0<2* t by lra.
have hInverse:(0<=((2* t)%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hDen.
have hScaled:= lee_wpmul2r hInverse hBound.
have hScalar:((((1+2* e)* t)%:E/(2* t)%:E)=(2^-1+e)%:E)%E.
  rewrite inver (gt_eqF hDen) -EFinM;apply:(congr1 (fun x:R=>x%:E)).
  have htN:t!=0 by rewrite gt_eqF.
  field;by rewrite htN.
rewrite hScalar in hScaled.
by rewrite /metric_ball_density /measure_restrict euclidean_unit_ball_volume1 expr1.
Qed.

(** Source for [circular_disc_upper_density_half]: the
    exact final value Theta*^1(H1 restricted to A,a)= 1/2
    in 3.3.19, p. 306. The proved upper estimate
    and the cofinal full-piece lower estimate in fact
    give this at every original a in A. *)
Theorem circular_disc_upper_density_half (a:E):A a ->
  upper_metric_density 1 (measure_restrict mu A) a=((1:R)/2)%:E.
Proof.
move=>ha;apply/eqP;rewrite eq_le.
apply/andP;split.
- exact:circular_disc_upper_density_at_most_half ha.
- exact:(@circular_disc_upper_density_at_least_half R H hH A hA a ha).
Qed.

(** Source for [circular_disc_upper_density_half_almost]:
    H1 almost every original a in A has actual upper
    one-density exactly one half, the final printed
    assertion of 3.3.19, p. 306. The stronger
    all-point theorem discharges the original null-exception
    formulation directly. *)
Theorem circular_disc_upper_density_half_almost:
  measure_almost_everywhere_on mu A [set a:E|
    upper_metric_density 1 (measure_restrict mu A) a=((1:R)/2)%:E].
Proof.
apply:(@measure_null_subset R E mu (@hausdorff_measure_is_measure R E 1) _ set0).
- move=>a [ha hBad];exact:hBad (circular_disc_upper_density_half ha).
- exact:measure_empty (@hausdorff_measure_is_measure R E 1).
Qed.
End Density.
