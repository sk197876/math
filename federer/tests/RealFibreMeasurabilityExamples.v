(** Project regressions for Federer 2.10.26, pp. 189-190. Real degrees
    allow an infinite compact fibre although the source has finite mass
    in the sum degree. Degree zero retains the singleton sublevel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealLineBoundedCompact
  RealHausdorffMeasure RealHausdorffMeasureLaws RealHausdorffNormalisation
  RealHausdorffLebesgue LebesgueScalarMeasure IntervalBumpFunctions
  RealHausdorffFibreCutoffs RealHausdorffFibreMeasurability
  CompactRealFibreMeasurability CountingMeasure CountingInjectionBound
  LipschitzUP LipschitzBasic NormMetricScaleContinuity
  TopologicalBorel BorelRegularMeasureUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasurableFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_half_measurable_infinite_compact_fibre]: project
    regression for both conclusions of Federer 2.10.26, pp. 189-190.
    Collapse the real unit interval to a point of an arbitrary metric
    target. The source has mass one in degree one, and its fibre has
    infinite mass in degree one-half. No target properness is used. *)
Theorem real_half_measurable_infinite_compact_fibre (R : realType)
    (Y : metricType R) (a : Y) (hp : (0 <= (1/2 : R))%R) :
    let X := real_line_metric R in
    let f : X -> Y := fun _ => a in
    let A : set X := `[0%R,1%R] in
    is_measure_measurable_function (@real_hausdorff_measure R Y (1/2 : R) hp)
      (partial_function_total (real_hausdorff_fibre_mass f A hp)) /\
    measure_almost_everywhere (@real_hausdorff_measure R Y (1/2 : R) hp)
      [set y | measure_measurable (@real_hausdorff_measure R X (1/2 : R) hp)
        (A `&` f @^-1` [set y])] /\
    real_hausdorff_fibre_mass f A hp a = +oo.
Proof.
move=> X f A.
have he : ((1/2 : R) + (1/2 : R))%R = 1%R by lra.
have hmassone (p : R) (hq : (0 <= p)%R) : p = 1%R ->
    @real_hausdorff_measure R X p hq A = 1.
  move=> h; subst p.
  by rewrite -[1%R]/(1%:R : R) real_hausdorff_measure_natural
    real_hausdorff_measure_one_lebesgue lebesgue_scalar_segment ?ler01 // subr0.
have hsum := hmassone ((1/2 : R)+(1/2 : R))%R (addr_ge0 hp hp) he.
have hA : measure_measurable
    (@real_hausdorff_measure R X ((1/2 : R)+(1/2 : R))%R (addr_ge0 hp hp)) A.
  apply: (borel_regular_borel_measurable
    (@real_hausdorff_measure_is_measure R X _ (addr_ge0 hp hp))
    (@real_hausdorff_measure_borel_regular R X _ (addr_ge0 hp hp))).
  apply: closed_borel_set; exact: segment_closed_real.
have hbound : is_metric_lipschitz_bound setT f 0%R.
  split; first exact: lexx.
  by move=> x z _ _; rewrite /f mdistxx mul0r.
have hfinite : @real_hausdorff_measure R X ((1/2 : R)+(1/2 : R))%R
    (addr_ge0 hp hp) A < +oo by rewrite hsum; exact: ltry.
have [hfun hfib] := @federer_2_10_26_real R X Y f
  (metric_lipschitz_of_bound hbound) A (1/2 : R) (1/2 : R) hp hp
  (@real_line_boundedly_compact R) hA hfinite.
split=> //; split=> //.
have hset : A `&` f @^-1` [set a] = A.
  apply/seteqP; split=> [x [hx _]|x hx] //; by split.
rewrite /real_hausdorff_fibre_mass hset.
apply/eqP; rewrite eq_le leey /= leNgt; apply/negP=> hfin.
have hlt : ((1/2 : R) < 1)%R by lra.
have hz := @real_hausdorff_finite_higher_degree_zero R X
  (1/2 : R) 1%R hp (ler01 : (0 <= 1 :> R)%R) A hlt hfin.
have hOne := hmassone 1%R (ler01 : (0 <= 1 :> R)%R) (erefl (1%R : R)).
by rewrite hOne in hz; move/eqP: hz; rewrite eqe oner_eq0.
Qed.

(** Source for [real_zero_fibre_closed_level_singleton]: project
    regression for the closed sublevels in Federer 2.10.26, p. 190.
    A compact singleton source and a constant map give mass one exactly
    at its image point. The zero sublevel is its Borel complement. *)
Theorem real_zero_fibre_closed_level_singleton (R : realType)
    (Y : metricType R) (a : Y) :
    let X := real_line_metric R in
    let f : X -> Y := fun _ => a in
    let A : set X := [set 0%R] in
    [set y | real_hausdorff_fibre_mass f A (lexx (0%R : R)) y <= 0] = ~` [set a] /\
    borel_set [set y | real_hausdorff_fibre_mass f A (lexx (0%R : R)) y <= 0].
Proof.
move=> X f A.
have hval y : real_hausdorff_fibre_mass f A (lexx (0%R : R)) y =
    if y == a then 1 else 0.
  case: ifP=> [/eqP hy|hy].
  - subst y.
    have he : A `&` f @^-1` [set a] = A.
      apply/seteqP; split=> [x [hx _]|x hx] //; by split.
    rewrite /real_hausdorff_fibre_mass he real_hausdorff_zero_counting.
    exact: counting_measure_singleton_value.
  - have he : A `&` f @^-1` [set y] = set0.
      apply/seteqP; split=> [x [_ hxy]|x []]; exfalso.
      have hya : y = a := esym hxy.
      by rewrite hya eqxx in hy.
    rewrite /real_hausdorff_fibre_mass he.
    exact: measure_empty (@real_hausdorff_measure_is_measure R X 0%R (lexx 0%R)).
split.
- apply/seteqP; split=> y.
  + move=> hy; change (is_true (real_hausdorff_fibre_mass f A (lexx (0%R : R)) y <= 0)) in hy.
    move=> hya; have he : y = a := hya.
    subst y; by rewrite hval eqxx lee_fin ler10 in hy.
  + move=> hy; change (is_true (real_hausdorff_fibre_mass f A (lexx (0%R : R)) y <= 0)).
    have hne : y != a by apply/eqP.
    by rewrite hval (negPf hne) lexx.
- have hf : continuous f.
    apply: (@metric_fixed_lipschitz_continuous R X Y f 0%R (lexx 0%R))=> x z.
    by rewrite /f mdistxx mul0r.
  exact: compact_real_fibre_mass_closed_level_borel hf (@compact_set1 X 0%R).
Qed.
