(** Federer (1969), 2.10.22, pp. 184–186:
    covering estimates for active positions of the compact
    limit array. Inactive positions contribute empty sets
    and zero auxiliary cost. All admissible active sets
    belong to the original compact family, so this
    does not change Caratheodory's construction. Source
    editions: CompactGeneratorCostUP.v and MaskedCompactGenerators.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  MaskedCompactGenerators MetricDiameter MetricScaleEnvelopeUP MetricScaleIndexedCover
  NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_masked_cover_bound]: supporting
    actual covering bound for prefixes and tails of
    the limit cover in 2.10.22, pp. 185–186.
    Any countable domain, including the empty one,
    is permitted. *)
Theorem metric_scale_masked_cover_bound (R : realType) (X : metricType R) (J : choiceType)
    (c : compact_metric_set X -> R) (delta : \bar R) (nu : set X -> \bar R)
    (u : J -> bool*compact_hausdorff_space X) (D : set J) (A : set X) :
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta nu ->
  (forall C, (0<=c C)%R) -> countable D ->
  (forall j, D j -> (u j).1 -> extended_metric_diameter (val (u j).2)<=delta) ->
  A `<=` \bigcup_(j in D) masked_compact_set (u j) ->
  nu A<=nonnegative_sum D (fun j=>(masked_compact_cost c (u j))%:E).
Proof.
move=> hn hc hD hd hcov.
pose E := D `&` [set j | (u j).1].
have hE : countable E := sub_countable (subset_card_le (fun j (hj : E j)=>hj.1)) hD.
have hcover : A `<=` \bigcup_(j in E) val (u j).2.
  move=> x hx; have [j hj hxj] := hcov x hx.
  rewrite /masked_compact_set in hxj.
  case hf: (u j).1 hxj=> hxj; last by case: hxj.
  exists j=> //; split=> //; exact hf.
have hc0 j : (0<=(c (u j).2)%:E)%E by rewrite lee_fin; exact: hc.
have hh := @metric_scale_envelope_indexed_cover R X (compact_metric_set X) J
  (fun C=>val C) (fun C=>(c C)%:E) delta nu hn A E (fun j=>(u j).2) hE
  (fun j _=> hc0 j) (fun j hj=>hd j hj.1 hj.2) hcover.
have he : nonnegative_sum D (fun j=>(masked_compact_cost c (u j))%:E)=
    nonnegative_sum E (fun j=>(c (u j).2)%:E).
  rewrite /E -nonnegative_sum_restrict; apply: nonnegative_sum_ext=> j hj.
  have hf : (j \in [set k | (u k).1])=(u j).1.
    apply/idP/idP; [by move=> /set_mem|by move=> h; apply: mem_set].
  rewrite /masked_compact_cost hf; by case: (u j).1.
by rewrite he.
Qed.
