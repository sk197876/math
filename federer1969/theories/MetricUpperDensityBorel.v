(** Federer (1969), 3.3.15, p. 299: the ORIGINAL upper-
    metric-density strata are Borel, with all premises proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MetricDensities MetricDensityCutoffOpen PositiveRadiusLimits
  PositiveRadiusReciprocalCutoffs ExtendedRealOrderTopology BorelFunctionUP TopologicalBorel
  StructureBorelOrderCriterion MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_upper_density_borel]: the Borel assertion
    for the actual E_i in Federer 3.3.15, p. 299, supporting the
    same density levels in 3.3.17, p. 300. Polynomial continuity
    and actual ball inclusions make every strict radial-supremum
    level open. Cofinal reciprocal cutoffs and strict threshold
    margins give the original limsup a countable Borel description.
    This supporting generalization needs only the measure laws,
    not Borel regularity, finite mass or source measurability. *)
Theorem metric_upper_density_borel (R:realType) (X:metricType R) m
    (mu:set X->\bar R):
  is_measure mu ->is_borel_function
    (fun x:X=>(upper_metric_density m mu x:extended_real_line R)).
Proof.
move=>hMu; apply:structure_borel_from_strict_superlevels=>b.
change (borel_set [set x:X|(b%:E<positive_radius_upper_limit
  (fun r:R=>metric_ball_density m mu x r))%E]).
rewrite positive_radius_upper_strict_superlevel.
apply:borel_set_countable_union (countableP setT) _=>j _.
apply:borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=>i _; rewrite positive_radius_supremum_strict_level.
  apply:open_borel_set; exact:metric_density_cutoff_superlevel_open hMu.
Qed.
