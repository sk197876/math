(** Federer (1969), 3.2.37, pp. 273--274: basic order, empty-set
    and closure laws for the actual upper and lower contents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume MinkowskiContents MetricOpenThickening MetricOpenThickeningClosure MeasureUP
  MeasureBasic PositiveRadiusLimitBounds PositiveRadiusLimitCongruence
  MetricDensityMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_tube_denominator_positive]: the positive
    normalizing factor alpha(n-m) r^(n-m) in Federer 3.2.37,
    p. 273, also at n=m and n=m=0. *)
Lemma minkowski_tube_denominator_positive (R:realType) (n m:nat) (r:R):
  (0<r)%R -> (0<euclidean_unit_ball_volume R (n-m)*r^+(n-m))%R.
Proof. move=>hr; apply:mulr_gt0; first exact:(euclidean_unit_ball_volumeE R (n-m)).2.
exact:exprn_gt0 _ hr. Qed.

(** Source for [minkowski_tube_quotient_nonnegative]: supporting
    nonnegative values of both contents, Federer 3.2.37, p. 273. *)
Lemma minkowski_tube_quotient_nonnegative (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (0<r)%R -> 0<=minkowski_tube_quotient m S r.
Proof.
move=>hr; rewrite /minkowski_tube_quotient; apply:mule_ge0.
- exact:(@measure_nonnegative R (inner_metric_space (@euclidean_inner_productP R n))
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _).
-
rewrite inve_ge0 lee_fin; exact:ltW (minkowski_tube_denominator_positive n m hr).
Qed.

(** Source for [minkowski_contents_nonnegative]: supporting order
    law for the definitions in Federer 3.2.37, p. 273. *)
Lemma minkowski_contents_nonnegative (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  0<=lower_minkowski_content m S /\ 0<=upper_minkowski_content m S.
Proof.
have hl:0<=lower_minkowski_content m S.
  apply:positive_radius_lower_nonnegative=>r hr.
  exact:(@minkowski_tube_quotient_nonnegative R n m S r hr).
split=>//; exact:le_trans hl (minkowski_contents_ordered m S).
Qed.

(** Source for [minkowski_contents_monotone]: supporting source
    monotonicity for both comparisons in Federer 3.2.37, p. 274. *)
Lemma minkowski_contents_monotone (R:realType) (n m:nat)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))): A `<=` B ->
  lower_minkowski_content m A<=lower_minkowski_content m B /\
  upper_minkowski_content m A<=upper_minkowski_content m B.
Proof.
move=>h; apply:positive_radius_limits_monotone=>r hr.
rewrite /minkowski_tube_quotient; apply:lee_wpmul2r.
- rewrite inve_ge0 lee_fin; exact:ltW (minkowski_tube_denominator_positive n m hr).
- apply:(@measure_mono R (inner_metric_space (@euclidean_inner_productP R n))
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)).
  exact:(@metric_open_thickening_monotone R
    (inner_metric_space (@euclidean_inner_productP R n)) A B r h).

Qed.

(** Source for [minkowski_contents_empty]: supporting empty-source
    boundary of Federer 3.2.37, p. 273; every actual open tube is empty. *)
Lemma minkowski_contents_empty (R:realType) (n m:nat):
  @upper_minkowski_content R n m set0=0 /\
  @lower_minkowski_content R n m set0=0.
Proof.
have he:forall r:R,(0<r)%R -> @minkowski_tube_quotient R n m set0 r=0.
  move=>r hr; rewrite /minkowski_tube_quotient metric_open_thickening_empty.
  by rewrite (measure_empty (euclidean_lebesgue_is_measure R n)) mul0e.
have [hu hl]:=positive_radius_limits_congr he.
rewrite /upper_minkowski_content /lower_minkowski_content hu hl.
exact:positive_radius_limits_constant.
Qed.

(** Source for [minkowski_contents_closure]: both functions assign
    the same number to S and clos S, Federer 3.2.37, p. 274.
    This includes nonmeasurable, unbounded and empty sources. *)
Lemma minkowski_contents_closure (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  upper_minkowski_content m (closure S)=upper_minkowski_content m S /\
  lower_minkowski_content m (closure S)=lower_minkowski_content m S.
Proof.
apply:positive_radius_limits_congr=>r hr.
by rewrite /minkowski_tube_quotient metric_open_thickening_closure.
Qed.
