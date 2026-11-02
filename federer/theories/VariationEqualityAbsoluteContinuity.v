(** Federer (1969), 2.9.20, p. 166: (2) implies (3). Localise the variation
    equality to subsegments, apply 2.4.11 to the finite absolute derivative
    integral, and sum on the disjoint interval interiors. Source context:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesImageMeasures RealAbsoluteContinuityUP OrderedIntervalFamilyUP
  OrderedIntervalFamilyUnion IntervalFamilyMassBound DerivativeVariationMeasure
  DerivativeVariationSmallSets VariationMassEqualityLocalization LebesgueScalarMeasure
  MeasureUP MeasureIntegralUniqueness BorelRegularMeasureUP TopologicalBorel
  IntervalBumpFunctions RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [variation_integral_equality_absolute_continuity]: direct
    implication (2)=>(3) of Federer 2.9.20, p. 166 The three-interval
    comparison forces equality of variation and the absolute derivative
    integral on every subsegment. The finite union has Lebesgue measure
    equal to its total cell length and its absolute derivative integral
    bounds the increment sum. The final estimate retains Federer's
    non-strict inequalities. The argument includes a=b. *)
Theorem variation_integral_equality_absolute_continuity (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<=b ->
  real_curve_variation_integral_equality g a b ->
  is_absolutely_continuous_real_curve g a b.
Proof.
move=> hg hp hab hEq.
pose nu := real_derivative_variation_measure psip psim.
have [hm [hrep [hz hbound]]] := @real_derivative_variation_measure_laws R g psip psim hg hp.
have hL := lebesgue_scalar_is_measure R.
have hclosed p q : measure_measurable (@lebesgue_scalar_measure R) `[p,q].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R p q).
have hOpen p q : measure_measurable (@lebesgue_scalar_measure R) `]p,q[.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; exact: interval_open.
have hmClosed p q : measure_measurable nu `[p,q] := (hrep _ (hclosed p q)).1.
have hmOpen p q : measure_measurable nu `]p,q[ := (hrep _ (hOpen p q)).1.
have hfull : nu `[a,b]=(curve_variation (g : R -> real_line_metric R) a b)%E.
  exact: esym (measure_integral_unique hEq (hrep _ (hclosed a b)).2).
have hsub u v : a<=u -> u<=v -> v<=b ->
    nu `[u,v]=(curve_variation (g : R -> real_line_metric R) u v)%E.
  move=> hau huv hvb.
  exact: variation_mass_equality_subsegment hg hmClosed hz
    (fun p q _ hpq _ => hbound p q hpq) hfull hau huv hvb.
have hinc u v : a<=u -> u<=v -> v<=b -> (`|g v-g u|%:E<=nu `[u,v])%E.
  move=> hau huv hvb; rewrite (hsub u v hau huv hvb).
  have hd := @curve_variation_ge_distance R [the metricType R of real_line_metric R] g u v huv.
  by rewrite real_line_metric_distanceE distrC in hd.
move=> e he.
have [d [hd hsmall]] := @real_derivative_variation_small_sets R g psip psim a b e hg hp hab he.
exists d; split=> // s hs hlen.
pose U := real_interval_family_open_union s.
have hU : measure_measurable (@lebesgue_scalar_measure R) U.
  exact: real_interval_family_open_union_measurable hL hOpen.
have hUsub := real_interval_family_open_union_subset hs.
have hUlen : (lebesgue_scalar_measure U<=d%:E)%E.
  by rewrite /U (@real_interval_family_open_union_length R a b s hs) lee_fin.
have hUsmall := hsmall U hU hUsub hUlen.
have hcost := @real_interval_family_increment_mass_bound R g nu a b s hm hmOpen hz hinc hs.
have hfinal := le_lt_trans hcost hUsmall.
by move: hfinal; rewrite lte_fin=> /ltW.
Qed.
