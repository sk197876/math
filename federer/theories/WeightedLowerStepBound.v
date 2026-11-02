(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting comparison
    with every assigned lower step function of 2.4.1–2.4.2, pp. 80–81.
    Positive fibres on the common good set have finite original measure when
    the weighted limit is finite. The Borel sandwich of 2.2.3, p. 61,
    transfers their measurability to the abstract restricted weighted
    measure. Finite disjoint additivity bounds the positive numerical
    variation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureStepFunctionUP MeasureStepFibres
  MeasureIntegralUP NonnegativeSum NonnegativeSumSupport NumericalSum NumericalSumOrder
  FatouNullRestriction MeasureFiniteAdditivity BorelRegularMeasureUP BorelNullTransfer
  WeightedRestrictionMeasure WeightedRestrictionSeparation WeightedRestrictionBounds WeightedMetricLimit
  CaratheodoryLimitUP CaratheodoryLimitMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_lower_step_bound]: supporting assigned
    lower-step inequality for the final paragraph of
    2.10.24, p. 188, using exactly the numerical-sum
    definition of 2.4.1, p. 80. The fixed input need
    not be measurable, the lower step may have
    countably many values, and the assigned sum is
    bounded through its positive variation. *)
Theorem weighted_lower_step_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> extended_real_line R)
    (u : partial_function X (real_line_metric R)) (b : \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> is_borel_regular_measure psi ->
  (forall x, 0<=f x) ->
  (forall B, weighted_restriction_measure S c psi (fun _=>1) B=psi B) ->
  weighted_metric_limit S c psi f< +oo ->
  is_measure_lower_function psi (partial_function_total f) u -> is_measure_step_integral psi u b ->
  b<=weighted_metric_limit S c psi f.
Proof.
move=> hpsi hc hr hf0 hind hfin [hu huf] hb.
have hm := caratheodory_limit_is_measure hpsi hc.
pose nu := weighted_restriction_measure S c psi f.
have hn : is_measure nu := weighted_restriction_is_measure hpsi hc hf0.
have hBorel B (hB : TopologicalBorel.borel_set B) : measure_measurable nu B :=
  @weighted_restriction_borel_measurable R X J S c psi f hpsi hc hf0 B hB.
have hnull B (hB : psi B=0) : nu B=0 := @weighted_restriction_null R X J S c psi f B hm hB.
pose E := partial_step_lower_locus u (partial_function_total f).
have hE : measure_almost_everywhere psi E := huf.
have hEm := measure_conull_set_measurable hm hE.
pose A (y : R) := partial_function_preimage u [set y] `&` E.
have hA y : measure_measurable psi (A y).
  exact: (@measure_measurable_intersection R X psi hm _ _
    (@measurable_real_fibre R X psi hm u (step_function_measurable hu) y) hEm).
have hAe y : psi (A y)=psi (partial_function_preimage u [set y]).
  exact: (@measure_conull_intersection_value R X psi hm E _ hE).
have hlevel y x (hx : A y x) : y%:E<=f x.
  have [[v [hv ev]] [w [z [hw [hz hwz]]]]] := hx.
  have he := partial_function_single_valued hw hv.
  have hvy : v=y := ev.
  have hfx : f x=z := hz.
  by rewrite -hfx he hvy in hwz.
have hAfin y (hy : (0<y)%R) : psi (A y)< +oo.
  exact: (@finite_weighted_limit_threshold_measure R X J S c psi f (A y) y
    hpsi hc hf0 hind hy (hlevel y) hfin).
have hAnu y (hy : (0<y)%R) : measure_measurable nu (A y).
  exact: (@borel_null_transfer_finite_measurable R X psi nu hm hn hr hBorel hnull
    (A y) (hA y) (hAfin y hy)).
pose d (y : R) := y%:E*psi (partial_function_preimage u [set y]).
pose p (y : R) := extended_positive_part (d y).
have hp0 y : (@setT R) y -> 0<=p y by move=> _; exact: extended_positive_part_nonnegative.
have hbp : b<=nonnegative_sum setT p.
  apply: (@numerical_sum_values_mono R R setT d p b (nonnegative_sum setT p))=> //.
  - move=> y _; by rewrite /p /extended_positive_part le_max lexx.
  - exact: numerical_sum_nonnegative hp0.
apply: le_trans hbp _; apply: nonnegative_sum_least=> C _.
pose D := [fset y in C | (0<y)%R].
have hsum : (\sum_(y <- C) p y)=\sum_(y <- D) y%:E*psi (A y).
  rewrite /D -big_fset_condE [in RHS]big_mkcond.
  apply: eq_big_seq=> y hy; have [hy0|hy0] := ltP 0%R y.
  - rewrite hAe /p /d /extended_positive_part max_l //.
    apply: mule_ge0; [rewrite lee_fin; exact: ltW hy0|exact: measure_nonnegative].
  - rewrite /p /d /extended_positive_part max_r //.
    apply: mule_le0_ge0; [rewrite lee_fin; exact hy0|exact: measure_nonnegative].
rewrite hsum.
have hDy y (hy : y \in D) : (0<y)%R.
  by move: hy; rewrite /D inE=> /andP[_ hy].
have hbound : \sum_(y <- D) y%:E*psi (A y)<=\sum_(y <- D) nu (A y).
  rewrite !big_seq; apply: lee_sum=> y hy.
  exact: (@weighted_restriction_threshold_bound R X J S c psi f (A y) y
    hm hc hind (hDy y hy) (hlevel y)).
apply: le_trans hbound _.
have hdis y z (hy : y \in D) (hz : z \in D) (hne : y!=z) x (hxy : A y x) (hxz : A z x) : False.
  have [[v [hv ev]] _] := hxy; have [[w [hw ew]] _] := hxz.
  have he := partial_function_single_valued hv hw.
  apply: (negP hne); apply/eqP; by rewrite -ev -ew.
have hadd := @measure_finite_disjoint_additivity R X R nu hn A D
  (fun y hy=>hAnu y (hDy y hy)) hdis.
rewrite -hadd -(@weighted_restriction_whole R X J S c psi f).
exact: (@measure_mono R X nu hn _ setT (fun x _=>Logic.I)).
Qed.
