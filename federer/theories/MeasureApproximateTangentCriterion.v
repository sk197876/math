(** Federer (1969), 3.2.16, p. 252:
    the directional upper-density characterization
    of approximate tangent vectors. The proof
    uses the defining intersection and local
    zero m-density monotonicity, without measurability
    or finite ball-mass hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureRestriction
  MetricDensities MetricDensityNumericalBounds MetricDensityZero TangentConeUP
  MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_approximate_tangent_directional_criterion]:
    the third display of Federer 3.2.16,
    p. 252. v is an approximate tangent
    vector exactly when every directional cone
    E(a,v,e) has strictly positive upper m-density. *)
Theorem measure_approximate_tangent_directional_criterion (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (phi : set X -> \bar R) m (a v : X) :
  is_measure phi ->
  (measure_approximate_tangent_cone hNX phi m a v <->
    forall e : R, (0<e)%R ->
      0<@upper_metric_density R (real_norm_metric_space hNX) m
        (measure_restrict phi (approximate_direction_cone NX a v e)) a).
Proof.
move=> hm; pose M := real_norm_metric_space hNX.
split.
- move=> hv e he.
  pose E := approximate_direction_cone NX a v e.
  have hnu := measure_restrict_is_measure hm E.
  have hnonneg := (@metric_densities_nonnegative R M m (measure_restrict phi E) a hnu).2.
  rewrite lt_neqAle hnonneg andbT.
  apply/negP=> /eqP hEq.
  have hZero : @upper_metric_density R M m (measure_restrict phi E) a=0 := esym hEq.
  pose S := ~` E.
  have hS : partial_function_graph (@metric_density R M m (measure_restrict phi (~` S))) a 0.
    rewrite /S setCK; exact: (@metric_density_zero_iff_upper_zero R M m _ a hnu).2 hZero.
  have [x [r [hx [hr [hxa hxv]]]]] := hv S hS e he.
  apply: hx; exists r; by split.
- move=> hPositive S hS e he.
  apply: contrapT=> hnone.
  pose E := approximate_direction_cone NX a v e.
  have hlocal : exists d : R, (0<d)%R /\
      forall x : M, (mdist (a : M) x<d)%R -> E x -> (~` S) x.
    exists e; split=> // x hdist [r [hr hxv]] hxS.
    apply: hnone; exists x,r; split=> //; split=> //; split=> //.
    change (is_true (NX (a-x)<e)%R) in hdist.
    by rewrite (real_seminorm_subtract hNX.1).
  have hE := @metric_restricted_density_zero_local_mono R M m phi E (~` S) a hm hlocal hS.
  have hnu := measure_restrict_is_measure hm E.
  have hu := (@metric_density_zero_iff_upper_zero R M m (measure_restrict phi E) a hnu).1 hE.
  have hp := hPositive e he.
  by rewrite hu ltxx in hp.
Qed.
