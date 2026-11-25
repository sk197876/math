(** Federer (1969), 2.10.24(2), pp. 187–188: equality under the joint
    enlargement and compact-cost hypotheses of 2.10.18 and 2.10.22.
    Continuity below is proved by 2.10.22, not added as a conclusion
    hypothesis. The weak containing-enlargement theorem additionally permits
    zero costs and supports the Hausdorff specialisations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds
  LipschitzFunctionCompact CompleteMetricUP CompactSetDistanceProfile CompactHausdorffMetric CompactGeneratorCostUP CompactCostContinuityBelow
  MetricScaleEnvelopeUP IncreasingProjectionLoss CaratheodoryLimitUP CaratheodoryWeakEnlargementUP
  CaratheodoryEnlargementGrowth DiameterEnlargements WeightedStrictEnlargementEquality
  WeightedMetricLimitUP WeightedMetricLimit WeightedContinuousScaleEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section CompactEquality.
Context (R : realType) (X : metricType R).
Local Notation F := [set A : set X | compact A /\ A!=set0].

(** Source for [weighted_compact_cost_equality]: supporting
    weak enlargement extension of 2.10.24(2),
    pp. 187–188. All nonempty compact generators,
    continuous finite costs positive on positive diameters,
    and bounded compactness have exactly the 2.10.22
    meaning. No finite-measure support hypothesis is added. *)
Theorem weighted_compact_cost_equality (c psi : set X -> \bar R)
    (cost : compact_metric_set X -> R) (E : set X -> set X) (k : R)
    (L : (X -> \bar R) -> \bar R) (f : X -> extended_real_line R) :
  metric_boundedly_compact X -> is_continuous_positive_compact_cost cost ->
  (forall C : compact_metric_set X, c (val C)=(cost C)%:E) ->
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>c (val C)) psi ->
  is_weighted_metric_limit (fun C : compact_metric_set X=>val C) (fun C=>c (val C)) psi L ->
  (forall x, 0<=f x) -> L f=measure_upper_integral psi (partial_function_total f).
Proof.
move=> hX hcost hc hE hp hL hf.
have hne S (hS : F S) : S<>set0.
  move=> he; have [x hx] := hS.2; by rewrite he in hx.
have hcf S (hS : F S) : c S< +oo.
  pose C : compact_metric_set X := exist _ S (mem_set hS).
  have hh := hc C; change (c S=(cost C)%:E) in hh; by rewrite hh ltry.
have hclosed S (hS : F S) : closed S := compact_closed (@metric_hausdorff R X) hS.1.
have hcont (d : R) nu (hd : (0<d)%R)
    (hn : is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>c (val C)) d%:E nu) :
    has_increasing_set_continuity nu.
  have he : (fun C : compact_metric_set X=>c (val C))=(fun C=>(cost C)%:E) by apply: funext.
  rewrite he in hn; move=> A hinc.
  exact: (@federer_2_10_22 R X cost hcost d nu A hX hd hn hinc).
exact: (@weighted_metric_limit_continuous_scale_equality R X F c psi E k L f hE hne (fun S hS _=>hcf S hS) hclosed hp hL hcont hf).
Qed.

(** Source for [federer_2_10_24_2]: direct second equality
    assertion of 2.10.24, pp. 187–188. The
    printed strict enlargement hypothesis is stated with
    its generator-domain requirement explicit, as in
    2.10.18. The actual weighted cutoff limit equals
    the upper integral, including infinite values. *)
Theorem federer_2_10_24_2 (c psi : set X -> \bar R)
    (cost : compact_metric_set X -> R) (eta : R) (f : X -> extended_real_line R) :
  metric_boundedly_compact X -> is_continuous_positive_compact_cost cost ->
  (forall C : compact_metric_set X, c (val C)=(cost C)%:E) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S< +oo) ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>c (val C)) psi ->
  (forall x, 0<=f x) ->
  weighted_metric_limit (fun C : compact_metric_set X=>val C) (fun C=>c (val C)) psi f=
    measure_upper_integral psi (partial_function_total f).
Proof.
move=> hX hcost hc hF hg hp hf.
have hc0 S (hS : F S) : 0<=c S.
  pose C : compact_metric_set X := exist _ S (mem_set hS).
  have hh := hc C; change (c S=(cost C)%:E) in hh; rewrite hh lee_fin.
  exact (@compact_cost_nonnegative_law R X cost hcost C).
have hE := strict_caratheodory_enlargement_is_weak (federer_caratheodory_enlargement_laws hc0 hF hg).
exact: (@weighted_compact_cost_equality c psi cost _ _ _ f hX hcost hc hE hp
  (weighted_metric_limit_specification _ _ _) hf).
Qed.
End CompactEquality.
