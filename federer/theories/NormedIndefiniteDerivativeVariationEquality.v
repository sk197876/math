(** Federer (1969), 2.9.22, pp. 167–168: extend the implication (1)=>(2) of
    2.9.20, p. 166. Each partition increment is bounded by the actual norm
    derivative integral on its cell. Null endpoints make the open interiors
    disjoint; finite additivity bounds the chain sum by the whole derivative
    variation mass. Take the original variation supremum and use the proved
    reverse inequality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveArcLength CurveVariationUP
  NormedCurveDerivativeUP NormedCurveAbsoluteContinuityUP NormedDerivativeVariationMeasure
  NormedPrimitiveIncrementBound DerivativeVariationMeasure MetricIntervalFamilyMassBound
  MetricIntervalFamilyNearVariation RealPartitionIntervalFamilies
  OrderedIntervalFamilyUP OrderedIntervalFamilyUnion StieltjesMonotone StieltjesImageMeasures
  MeasureUP MeasureBasic MeasureAlmostUP MeasureSubsetIntegral ExtendedRealBounds
  LebesgueScalarMeasure RealMetricBackground BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [normed_indefinite_derivative_integral_variation_equality]:
    direct (1)=>(2) part of Federer 2.9.22, pp. 167–168,
    extending 2.9.20, p. 166. The proof follows its partition
    supremum and derivative-mass comparison, now with the proved
    vector integral norm bound. Repeated partition terms and the
    boundary a=b are included. The actual norm integrand preserves
    the derivative's exact partial domain throughout. *)
Theorem normed_indefinite_derivative_integral_variation_equality (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists w : E, has_normed_curve_derivative N g x w] -> (a<=b)%R ->
  normed_curve_indefinite_derivative_integral hN g a b ->
  normed_curve_variation_integral_equality hN g a b.
Proof.
move=> hY hg he hab hF.
have hs (u v : R) : (u<=v)%R -> (arc_length g u<=arc_length g v)%R :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg u v.
have hfin := @monotone_locally_finite_variation R (arc_length g) hs.
have [psip [psim hp]] := @induced_measure_pair_exists R (arc_length g) hfin.
pose nu := real_derivative_variation_measure psip psim.
have [hm [hrep [hz hbound]]] := @normed_derivative_variation_measure_laws R E N hN g psip psim hg he hp.
have hL := lebesgue_scalar_is_measure R.
have hclosed p q : measure_measurable (@lebesgue_scalar_measure R) `[p,q].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R p q).
have hopen p q : measure_measurable nu `]p,q[.
  apply: (hrep `]p,q[ _).1.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set.
  have hEq : (`]p,q[ : set (real_line_metric R))=real_open_interval p q.
    apply/seteqP; split=> z.
    - rewrite /= in_itv /= => /andP [hpz hzq]; by split.
    - move=> [hpz hzq]; by rewrite /= in_itv /= hpz hzq.
  rewrite hEq; exact: real_open_interval_open.
have hinc u v : (a<=u)%R -> (u<=v)%R -> (v<=b)%R -> (N (g v-g u))%:E<=nu `[u,v].
  move=> hau huv hvb.
  exact (@normed_primitive_increment_mass_bound R E N hN g psip psim a b u v
    hY hg he hp hF hau huv hvb).
have hV : curve_variation g a b<=nu `[a,b].
  apply: extended_real_sup_least=> z [s [hPart ->]].
  have [hsort [hn [hh hl]]] := hPart.
  pose t := real_partition_interval_cells s.
  have ht : is_ordered_real_interval_family a b t.
    apply: real_partition_cells_ordered hsort _ _; by rewrite ?hh ?hl.
  have hincMetric u v : (a<=u)%R -> (u<=v)%R -> (v<=b)%R -> (mdist (g u) (g v))%:E<=nu `[u,v].
    move=> hau huv hvb.
    rewrite real_norm_metric_distanceE (real_seminorm_subtract hN.1).
    exact: hinc.
  have hb := @metric_interval_family_increment_mass_bound R
    [the metricType R of real_norm_metric_space hN] g nu a b t hm hopen hz hincMetric ht.
  have hlen := @metric_partition_cells_increments R [the metricType R of real_norm_metric_space hN]
    g s hsort.
  rewrite /t hlen in hb.
  apply: le_trans hb _.
  exact (@measure_mono R R nu hm (real_interval_family_open_union t) `[a,b]
    (@real_interval_family_open_union_subset R a b t ht)).
have hEq : curve_variation g a b=nu `[a,b].
  by apply/eqP; rewrite eq_le hV (hbound a b hab).
rewrite /normed_curve_variation_integral_equality hEq.
exact (hrep `[a,b] (hclosed a b)).2.
Qed.
