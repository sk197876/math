(** Federer (1969), 3.3.18, p. 301: two finite positive
    measure comparisons identify the actual approximate tangent cones. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction
  PartialFunctionUP MetricDensities DominatedMetricZeroDensity MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [comparable_measure_approximate_tangents]: the second
    tangent equality in the proof of Federer 3.3.18, p. 301.
    Independent all-subset comparisons with positive finite constants
    give exactly the same full-density test sets. The intersection
    definition of the ORIGINAL tangent cone then gives equality.
    No tangent, density-one or rectifiability conclusion is a premise. *)
Theorem comparable_measure_approximate_tangents (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) m (mu nu:set X->\bar R) (a:X) (c d:R):
  is_measure mu ->is_measure nu ->(0<c)%R ->(0<d)%R ->
  (forall A,mu A<=c%:E*nu A) ->(forall A,nu A<=d%:E*mu A) ->
  measure_approximate_tangent_cone hNX mu m a=
    measure_approximate_tangent_cone hNX nu m a.
Proof.
move=>hMu hNu hc hd hMuNu hNuMu.
pose M:=real_norm_metric_space hNX.
have hTest S:
    partial_function_graph (@metric_density R M m (measure_restrict mu (~` S))) a 0 <->
    partial_function_graph (@metric_density R M m (measure_restrict nu (~` S))) a 0.
  split.
  - exact:(@dominated_metric_zero_density R M m (measure_restrict nu (~` S))
      (measure_restrict mu (~` S)) a d (measure_restrict_is_measure hNu _)
      (measure_restrict_is_measure hMu _) (ltW hd) (fun A=>hNuMu ((~` S) `&` A))).
  - exact:(@dominated_metric_zero_density R M m (measure_restrict mu (~` S))
      (measure_restrict nu (~` S)) a c (measure_restrict_is_measure hMu _)
      (measure_restrict_is_measure hNu _) (ltW hc) (fun A=>hMuNu ((~` S) `&` A))).
apply/seteqP; split=>v hv S hS.
- exact:hv S ((hTest S).2 hS).
- exact:hv S ((hTest S).1 hS).
Qed.
