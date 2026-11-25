(** Federer (1969), 3.2.16, pp. 252–253:
    supporting zero m-density laws for an arbitrary
    measure. These use the metric normalization
    alpha(m) r^m of 2.10.19, not a quotient by
    the measure's own ball mass. No positive or
    finite measure of all balls is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MetricDensities MetricDensityNumericalBounds MetricClosedBalls EuclideanBallVolume
  PositiveRadiusLimits PositiveRadiusLimitBounds ExtendedRealBounds
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_density_zero_iff_upper_zero]:
    the zero m-density conditions in Federer 3.2.16,
    pp. 252–253, are equivalent to zero upper density,
    by nonnegativity and the ordered density limits. *)
Lemma metric_density_zero_iff_upper_zero (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) a :
  is_measure mu ->
  (partial_function_graph (metric_density m mu) a 0 <-> upper_metric_density m mu a=0).
Proof.
move=> hm; split; first by move=> [hu _].
move=> hu; split=> //.
have hl := metric_densities_ordered m mu a.
rewrite hu in hl.
apply/eqP; rewrite eq_le hl (@metric_densities_nonnegative R X m mu a hm).1.
reflexivity.
Qed.

(** Source for [metric_upper_density_zero_iff_small]:
    supporting small-ball criterion for the zero
    m-density exceptional sets in Federer 3.2.16,
    pp. 252–253. It retains arbitrary measures
    and the positive-radius domain of normalization. *)
Lemma metric_upper_density_zero_iff_small (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) a :
  is_measure mu ->
  (upper_metric_density m mu a=0 <->
    forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
      forall r : R, (0<r<d)%R -> metric_ball_density m mu a r<=e%:E).
Proof.
move=> hm; split.
- move=> hu e he.
  have hlt : positive_radius_upper_limit (metric_ball_density m mu a)<e%:E.
    change (upper_metric_density m mu a<e%:E); by rewrite hu lte_fin.
  have [d [hd hs]] := (@positive_radius_upper_lt_iff R (metric_ball_density m mu a) e%:E).1 hlt.
  exists d; split=> // r hr.
  have hv : positive_radius_values (metric_ball_density m mu a) d (metric_ball_density m mu a r).
    exists r; by split.
  exact: ltW (le_lt_trans (extended_real_sup_upper hv) hs).
- move=> hb.
  have hnonneg := (@metric_densities_nonnegative R X m mu a hm).2.
  apply/eqP; rewrite eq_le hnonneg andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> n.
  have he : (0<(n.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have [d [hd hs]] := hb _ he.
  rewrite add0r; exact: (positive_radius_upper_eventual_bound hd hs).
Qed.

(** Source for [metric_restricted_density_zero_local_mono]:
    supporting local inclusion of exceptional cones
    in Federer 3.2.16, p. 252. An inclusion
    on one ball around a suffices for zero density
    transport, without measurability of either set. *)
Theorem metric_restricted_density_zero_local_mono (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A B : set X) a :
  is_measure mu ->
  (exists d : R, (0<d)%R /\ forall x, (mdist a x<d)%R -> A x -> B x) ->
  partial_function_graph (metric_density m (measure_restrict mu B)) a 0 ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0.
Proof.
move=> hm [d [hd hAB]] hB.
pose nuA := measure_restrict mu A.
pose nuB := measure_restrict mu B.
have hmA : is_measure nuA := measure_restrict_is_measure hm A.
have hmB : is_measure nuB := measure_restrict_is_measure hm B.
apply: (@metric_density_zero_iff_upper_zero R X m nuA a hmA).2.
apply: (@metric_upper_density_zero_iff_small R X m nuA a hmA).2=> e he.
have hBu := (@metric_density_zero_iff_upper_zero R X m nuB a hmB).1 hB.
have [s [hs hsmall]] := (@metric_upper_density_zero_iff_small R X m nuB a hmB).1 hBu e he.
exists (Num.min d s)%R; split; first by rewrite lt_min hd hs.
move=> r /andP [hr hmin].
have hmd : (Num.min d s<=d)%R by rewrite ge_min lexx.
have hrd : (r<d)%R := lt_le_trans hmin hmd.
have hrs : (r<s)%R.
  apply: lt_le_trans hmin _; by rewrite ge_min lexx orbT.
have hnum : mu (A `&` metric_closed_ball a r)<=mu (B `&` metric_closed_ball a r).
  apply: (@measure_mono R X mu hm)=> x [hx hball]; split=> //.
  apply: (hAB x _ hx); exact: le_lt_trans hball hrd.
have hden : 0<=((euclidean_unit_ball_volume R m*r^+m)%R%:E)^-1.
  rewrite inve_ge0 lee_fin; exact: ltW (metric_ball_density_denominator_positive m hr).
have hbound : metric_ball_density m nuA a r<=metric_ball_density m nuB a r.
  rewrite /metric_ball_density /nuA /nuB /measure_restrict.
  exact (lee_wpmul2r hden hnum).
apply: le_trans hbound _; apply: hsmall; by apply/andP; split.
Qed.
