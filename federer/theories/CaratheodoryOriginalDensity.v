(** Federer 2.10.17(3), p. 179, with the original partial quotient of
    2.1.1. The uncut covering measure of a generator is bounded by its
    cost, from 2.10.1. Thus zero cost forces zero numerator here. This
    special fact permits reuse of the existing subcritical-locus proof;
    it does not repair the false arbitrary-numerator assertion of (2). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction
  MeasureDerivates PartialFunctionUP ExtendedRealBounds
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleWeightedBound
  MetricScaleCutoffCost CaratheodoryLimitUP CaratheodoryLimitMeasure
  CaratheodoryDensityQuotient CaratheodoryDensityFunction
  CaratheodoryDensityUpperBound CaratheodoryDensityLowerBound
  CoveringRelationUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_original_subcritical_transfer]: supporting
    connection for Federer 2.10.17(3), p. 179. If every zero-cost related
    generator has zero restricted mass, filling its undefined quotient
    with zero preserves a strict upper limit below one. A small-scale
    supremum is bounded by the maximum of the original supremum and zero.
    The original quotient itself remains partial. *)
Lemma caratheodory_original_subcritical_transfer (R : realType)
    (X : metricType R) (mu c : set X -> \bar R)
    (C : X -> set X -> Prop) (A : set X) x :
    (forall S, C x S -> c S=0 -> mu (A `&` S)=0) ->
    covering_upper_limit C (measure_ratio_function (measure_restrict mu A) c) x<1 ->
    covering_upper_limit C (caratheodory_density_function mu c A) x<1.
Proof.
move=> hz hu.
have [e [he hs]] := (covering_upper_limit_lt_iff _ _ _ _).1 hu.
pose b := extended_real_sup
  (covering_value_range C (measure_ratio_function (measure_restrict mu A) c) x e).
have hb : Order.max b 0<1 by rewrite gt_max hs lte_fin ltr01.
apply: le_lt_trans _ hb.
apply: le_trans (covering_upper_limit_le_level C
  (caratheodory_density_function mu c A) x he) _.
apply: extended_real_sup_least => y [S [hS [hd hy]]].
case: (eqVneq (c S) 0) => [hc|hc].
- have hm := hz S hS hc.
  move: hy; rewrite caratheodory_density_function_graph hm hc
    caratheodory_density_divide_zero_zero => -[<-].
  by rewrite le_max lexx orbT.
- have hg : partial_function_graph
      (measure_ratio_function (measure_restrict mu A) c) S y.
    move: hy; rewrite caratheodory_density_function_graph
      (caratheodory_density_divide_nonzero (mu (A `&` S)) hc).
    by [].
  have hr : covering_value_range C
      (measure_ratio_function (measure_restrict mu A) c) x e y.
    by exists S; split=> //; split.
  apply: le_trans (extended_real_sup_upper hr) _.
  by rewrite le_max lexx.
Qed.

(** Source for [uncut_caratheodory_zero_cost_restriction]: supporting
    original-numerator fact in Federer 2.10.17(3), p. 179. The definition
    in 2.10.1, p. 170, gives phi_infinity(S)<=zeta(S) by the singleton
    cover. Monotonicity gives the same bound after intersection with A,
    so a zero-cost generator has zero restricted uncut mass. *)
Lemma uncut_caratheodory_zero_cost_restriction (R : realType)
    (X : metricType R) (F : set (set X)) (c omega : set X -> \bar R)
    (A : set X) :
    (forall S, F S -> 0<=c S) ->
    is_metric_scale_envelope (fun j : set_type F => val j)
      (fun j => c (val j)) +oo omega ->
    forall S, F S -> c S=0 -> omega (A `&` S)=0.
Proof.
move=> hc ho S hS hz.
pose J := [the choiceType of set_type F].
pose S0 : J := @exist (set X) (fun T => T \in F) S (mem_set hS).
have hm := @metric_scale_envelope_is_measure R X J
  (fun j => val j) (fun j => c (val j)) +oo omega ho
  (fun j => hc _ (set_valP j)).
have hgen := @metric_scale_generator_bound R X J
  (fun j => val j) (fun j => c (val j)) +oo omega S0 ho
  (hc S hS) (leey _).
have hbound : omega S<=c S := hgen.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
rewrite -hz; apply: le_trans _ hbound.
apply: (@measure_mono R X omega hm) => x [hx hSx]; exact: hSx.
Qed.

(** Source for [federer_2_10_17_3_original]: direct original partial-
    quotient assertion of Federer 2.10.17(3), p. 179. Retain the printed
    intersection-cost condition, fine covering relation, finite positive-
    cutoff approximations and the two bounds 0<=upper<1. The numerator
    is the uncut covering measure restricted to A, as printed. *)
Theorem federer_2_10_17_3_original (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R)
    (omega psi : set X -> \bar R) (A : set X) :
    (forall S, F S -> 0<=c S) ->
    (forall S T, F S -> F T -> F (S `&` T) /\ c (S `&` T)<=c T) ->
    (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
    is_metric_scale_envelope (fun j : set_type F => val j)
      (fun j => c (val j)) +oo omega ->
    is_caratheodory_limit (fun j : set_type F => val j)
      (fun j => c (val j)) psi ->
    (forall delta : \bar R, 0<delta ->
      metric_scale_envelope (fun j : set_type F => val j)
        (fun j => c (val j)) delta A < +oo) ->
    psi [set x | A x /\
      0<=covering_upper_limit (caratheodory_family_relation F)
        (measure_ratio_function (measure_restrict omega A) c) x /\
      covering_upper_limit (caratheodory_family_relation F)
        (measure_ratio_function (measure_restrict omega A) c) x<1]=0.
Proof.
move=> hc hclosed hf ho hpsi hfinite.
have hn := @caratheodory_density_subcritical_null R X F c omega psi A
  hc hclosed ho hpsi hfinite.
have hm := @caratheodory_limit_is_measure R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) psi hpsi
  (fun j => hc _ (set_valP j)).
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
rewrite -hn; apply: (@measure_mono R X psi hm) => x [hx [_ hu]].
split=> //.
apply: (@caratheodory_original_subcritical_transfer R X omega c
  (caratheodory_family_relation F) A x) => // S [hS _] hz.
exact: (@uncut_caratheodory_zero_cost_restriction R X F c omega A hc ho S hS hz).
Qed.
