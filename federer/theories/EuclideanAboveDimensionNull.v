(** Federer (1969), 2.10.39, printed p. 199: the corollary also allows
    positive degrees above n, since 2.10.3, pp. 171–172, does not impose
    m<=n. These supporting nullity theorems follow from dimension drop in
    2.10.2, p. 171, and the ambient-degree equality of 2.10.35, p. 197.
    Countably many bounded balls cover the space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanClosedBallVolume
  EuclideanHausdorffLebesgue HausdorffMeasure HausdorffDimensionDrop HausdorffSphericalComparison
  MetricClosedBalls MeasureUP MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_hausdorff_above_dimension_zero]: supporting
    above-ambient case of 2.10.39, p. 199,
    from 2.10.2, p. 171, and 2.10.35,
    p. 197. Every target is allowed, without a
    measurability, boundedness or sigma-finiteness premise. *)
Theorem euclidean_hausdorff_above_dimension_zero (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (n<m)%N -> @hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A=0.
Proof.
move=> hnm.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose B k := @metric_closed_ball R [the metricType R of E] (0%R : E) (k%:R : R).
have hball k : @hausdorff_measure R [the metricType R of E] m (B k)=0.
  apply: (@hausdorff_finite_mass_higher_degree_zero R [the metricType R of E] n m (B k) hnm).
  rewrite (@euclidean_hausdorff_spherical_lebesgue R n (B k)).1.
  apply: le_lt_trans (@euclidean_closed_ball_volume_upper R n (0%R : E)
    (k%:R : R) (ler0n _ _)) _.
  exact: ltry.
have hc : A `<=` \bigcup_(k in @setT nat) B k.
  move=> x hx; pose k := Num.bound (mdist (0%R : E) x).
  have hk : (mdist (0%R : E) x<k%:R)%R := archi_boundP (mdist_ge0 _ _).
  exists k=> //; exact: ltW hk.
have hcnt : countable (@setT nat) by exact: countableP.
have hm := @hausdorff_measure_is_measure R [the metricType R of E] m.
have hb := @measure_indexed_cover R [the choiceType of E] [the choiceType of (nat : Type)]
  _ hm A setT B hcnt hc.
rewrite (nonnegative_sum_zero (fun k _=>hball k)) in hb.
by apply/eqP; rewrite eq_le hb (measure_nonnegative hm).
Qed.

(** Source for [euclidean_spherical_above_dimension_zero]: supporting
    above-ambient case of 2.10.39, p. 199.
    Use the preceding dimension-drop consequence and the
    spherical/Hausdorff comparison of 2.10.2(2), p. 171.
    Dimension zero is included when m is positive. *)
Theorem euclidean_spherical_above_dimension_zero (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (n<m)%N -> @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A=0.
Proof.
move=> hnm.
have hh := @spherical_measure_le_double_hausdorff_measure R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A.
rewrite (@euclidean_hausdorff_above_dimension_zero R n m A hnm) mule0 in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (@spherical_measure_is_measure R _ m)).
Qed.
