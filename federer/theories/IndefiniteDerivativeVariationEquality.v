(** Federer (1969), 2.9.20, p. 166: (1) implies (2). Bound every partition
    sum by the absolute derivative integral, take the variation supremum,
    and use 2.9.19 for the reverse inequality. Source context:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesImageMeasures RealAbsoluteContinuityUP RealSegmentIntegralDifference
  DerivativeAbsoluteIntegralBound DerivativeVariationMeasure IntervalFamilyMassBound
  OrderedIntervalFamilyUP OrderedIntervalFamilyUnion RealPartitionIntervalFamilies
  RealCurveDerivativeIntegrands ExtendedRealBounds LebesgueScalarMeasure MeasureUP
  MeasureBasic MeasureIntegralUniqueness MeasureSubsetIntegral TopologicalBorel
  BorelRegularMeasureUP IntervalBumpFunctions RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [indefinite_derivative_integral_variation_equality]: direct
    implication (1)=>(2) of Federer 2.9.20, p. 166 Subtract finite
    indefinite integrals on each cell, apply the absolute integral bound,
    and sum over disjoint interiors. Repeated partition terms are removed
    with no change to the length sum. The opposite inequality is 2.9.19. The
    argument also includes the degenerate segment a=b. *)
Theorem indefinite_derivative_integral_variation_equality (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> (a<=b)%R ->
  real_curve_indefinite_derivative_integral g a b ->
  real_curve_variation_integral_equality g a b.
Proof.
move=> hg hp hab hF.
pose nu := real_derivative_variation_measure psip psim.
have [hm [hrep [hz hbound]]] := @real_derivative_variation_measure_laws R g psip psim hg hp.
have hL := lebesgue_scalar_is_measure R.
have hclosed p q : measure_measurable (@lebesgue_scalar_measure R) `[p,q].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R p q).
have hopen p q : measure_measurable nu `]p,q[.
  apply: (hrep `]p,q[ _).1.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; exact: interval_open.
have hinc u v : (a<=u)%R -> (u<=v)%R -> (v<=b)%R -> `|g v-g u|%:E<=nu `[u,v].
  move=> hau huv hvb.
  have hI := @indefinite_derivative_integral_subsegment R g a b u v hF hau huv hvb.
  have [J [hJ hb]] := @derivative_subset_integral_absolute_bound R g
    (@lebesgue_scalar_measure R) `[u,v] (g v-g u) hL hI.
  have he := measure_integral_unique hJ (hrep `[u,v] (hclosed u v)).2.
  by rewrite he in hb.
have hV : curve_variation (g : R -> real_line_metric R) a b<=nu `[a,b].
  apply: extended_real_sup_least=> z [s [hs ->]].
  have [hsort [hn [hh hl]]] := hs.
  pose t := real_partition_interval_cells s.
  have ht : is_ordered_real_interval_family a b t.
    apply: real_partition_cells_ordered hsort _ _; by rewrite ?hh ?hl.
  have hb := @real_interval_family_increment_mass_bound R g nu a b t hm hopen hz hinc ht.
  have hlen := @real_partition_cells_increments R g s hsort.
  rewrite /t hlen in hb.
  apply: le_trans hb _.
  exact (@measure_mono R R nu hm (real_interval_family_open_union t) `[a,b]
    (@real_interval_family_open_union_subset R a b t ht)).
have he : curve_variation (g : R -> real_line_metric R) a b=nu `[a,b].
  by apply/eqP; rewrite eq_le hV (hbound a b hab).
rewrite /real_curve_variation_integral_equality he.
exact: (hrep `[a,b] (hclosed a b)).2.
Qed.
